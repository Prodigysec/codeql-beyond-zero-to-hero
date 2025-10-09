/**
 * @name Class pollution via dynamic attribute access
 * @description Detects when user-controlled data flows into getattr then setattr,
 *              allowing attackers to manipulate object attributes.
 * @kind path-problem
 * @id py/class-pollution
 * @problem.severity error
 * @precision medium
 * 
 * Note: - Uses DataFlow configuration to precisely model the flow steps
*/

import python
import semmle.python.dataflow.new.DataFlow
import MyFlow::PathGraph

// Source
class PreprocessingSource extends DataFlow::ParameterNode {
  PreprocessingSource() {
    exists(Function f |
      f.getName() = "__init__" and
      this = DataFlow::parameterNode(f.getArgByName("preprocessing"))
    )
  }
}

// Sink
class SetAttrSink extends DataFlow::CallCfgNode {
  SetAttrSink() {
    exists(Call c |
      c.getFunc().(Name).getId() = "setattr" and
      this = DataFlow::exprNode(c)
    )
  }
}

// Model flow from parameter to self._preprocessing attribute
predicate fieldAssignFromParam(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
    exists(PreprocessingSource p, Assign assign, Attribute lhs, Name rhs |
        assign.getValue() = rhs and
        assign.getATarget() = lhs and
        rhs.getId() = "preprocessing" and
        lhs.getAttr() = "_preprocessing" and
        lhs.getObject().(Name).getId() = "self" and
        nodeFrom = p and
        nodeTo   = DataFlow::exprNode(lhs)
    )
}

// Flow from self._preprocessing attribute writes to reads
predicate instanceAttributeFlow(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(Attribute write, Attribute read |
    // Write in __init__: self._preprocessing = ...
    write.getAttr() = "_preprocessing" and
    write.getObject().(Name).getId() = "self" and
    exists(Assign a | a.getATarget() = write) and
    
    // Read in __getitem__: self._preprocessing.items()
    read.getAttr() = "_preprocessing" and
    read.getObject().(Name).getId() = "self" and
    
    // Both in the same class
    write.getScope().(Function).getEnclosingScope() = 
    read.getScope().(Function).getEnclosingScope() and
    
    // Flow
    nodeFrom = DataFlow::exprNode(write) and
    nodeTo = DataFlow::exprNode(read)
  )
}


predicate fieldToItemsCall(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(Call itemsCall, Attribute recv |
    // Match self._preprocessing.items()
    itemsCall.getFunc().(Attribute).getAttr() = "items" and
    recv = itemsCall.getFunc().(Attribute).getObject() and
    recv.getAttr() = "_preprocessing" and
    recv.getObject().(Name).getId() = "self" and
    
    // Flow from the receiver to the call result
    nodeFrom = DataFlow::exprNode(recv) and
    nodeTo   = DataFlow::exprNode(itemsCall)
  )
}


predicate itemsToLoopVars(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(For f, Call itemsCall, Attribute recv, Tuple target |
    f.getIter() = itemsCall and
    itemsCall.getFunc().(Attribute).getAttr() = "items" and
    recv = itemsCall.getFunc().(Attribute).getObject() and
    recv.getAttr() = "_preprocessing" and
    recv.getObject().(Name).getId() = "self" and
    nodeFrom = DataFlow::exprNode(itemsCall) and
    // Flow to the first element of the tuple (field)
    target = f.getTarget() and
    nodeTo = DataFlow::exprNode(target.getElt(0))
  )
}


/**
 * Flow step: field string → attr (via split + subscript).
 * string transformation step
 */
predicate fieldToAttr(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(
    Call splitCall, Assign accPathAssign, Name accPathDef,
    Assign attrAssign, Name attrDef, Name accPathUse,
    Subscript sub, UnaryExpr unary, IntegerLiteral lit,
    Call setattrCall, Name attrUse
  |
    accPathAssign.getValue() = splitCall and
    accPathAssign.getATarget() = accPathDef and
    splitCall.getFunc().(Attribute).getAttr() = "split" and
    nodeFrom = DataFlow::exprNode(splitCall.getFunc().(Attribute).getObject()) and
    
    attrAssign.getValue() = sub and
    attrAssign.getATarget() = attrDef and
    sub.getObject() = accPathUse and
    sub.getIndex() = unary and
    unary.getOp() instanceof USub and
    unary.getOperand() = lit and
    lit.getValue() = 1 and
    accPathDef.getId() = accPathUse.getId() and
    
    // Connect to setattr usage
    setattrCall.getFunc().(Name).getId() = "setattr" and
    setattrCall.getArg(1) = attrUse and
    attrUse.getId() = attrDef.getId() and
    
    nodeTo = DataFlow::exprNode(attrUse)
  )
}


// Connect source to sink with additional steps between them
module MyFlowConfig implements DataFlow::ConfigSig {

  predicate isSource(DataFlow::Node source) {
    source instanceof PreprocessingSource
  }


  predicate isSink(DataFlow::Node sink) {
    // class-pollution: attacker controls the attribute *name* - 2nd arg
    exists(SetAttrSink call |
      sink = call.getArg(1)
    )
  }


  predicate isAdditionalFlowStep(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
    fieldAssignFromParam(nodeFrom, nodeTo)
    or
    instanceAttributeFlow(nodeFrom, nodeTo)
    or
    fieldToItemsCall(nodeFrom, nodeTo)
    or
    itemsToLoopVars(nodeFrom, nodeTo)
    or
    fieldToAttr(nodeFrom, nodeTo)
  }
}
module MyFlow = DataFlow::Global<MyFlowConfig>;

from MyFlow::PathNode source, MyFlow::PathNode sink
where MyFlow::flowPath(source, sink)
select sink.getNode(), source, sink, "This $@ flows to 2nd arg of setattr", source.getNode(),
  "resulting in class pollution"