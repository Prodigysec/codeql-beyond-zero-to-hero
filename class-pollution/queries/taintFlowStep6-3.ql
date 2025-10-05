/** Flow to setattr and getattr */

import python
import semmle.python.dataflow.new.DataFlow
import MyFlow::PathGraph

/* Add to data-flow configuration */
class PreprocessingSource extends DataFlow::ParameterNode {
  PreprocessingSource() {
    exists(Function f |
      f.getName() = "__init__" and
      f.getLocation().getFile().getBaseName() = "torch_dataset.py" and
      this = DataFlow::parameterNode(f.getArgByName("preprocessing"))
    )
  }
}

// Your sink node (placeholder: you’ll define what’s “dangerous” later)
class SetAttrSink extends DataFlow::CallCfgNode {
  SetAttrSink() {
    exists(Call c |
      c.getFunc().(Name).getId() = "setattr" and
      c.getLocation().getFile().getBaseName() = "torch_dataset.py" and
      this = DataFlow::exprNode(c)
    )
  }
}

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


// FOR DATA POLLUTION
// predicate callThroughCallable(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
//   exists(Call c, Name fn |
//     c.getFunc() = fn and
//     fn.getId() = "preprocess" and
//     // Flow from first argument to return value
//     nodeFrom = DataFlow::exprNode(c.getArg(0)) and
//     nodeTo = DataFlow::exprNode(c)
//   )
// }


/**
 * Flow step: field string → attr (via split + subscript).
 * string transformation step
 */
predicate fieldToAttr(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(
    Call splitCall, Assign accPathAssign, Name accPathDef,
    Assign attrAssign, Name attrDef, Name accPathUse,  // ADDED accPathUse here
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


// REDUNDANT
/**
 * Models flow of attribute names into setattr (class pollution sink).
 * Connects the variable `attr` (derived from field) to the second argument of `setattr`.
 */
// predicate attrToSetattrArg(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
//   exists(Call c, Name attrVar |
//     c.getFunc().(Name).getId() = "setattr" and
//     c.getArg(1) = attrVar and
//     attrVar.getId() = "attr" and
//     // Flow from the attr variable to its use in setattr
//     nodeFrom = DataFlow::exprNode(attrVar) and
//     nodeTo = DataFlow::exprNode(c.getArg(1))
//   )
// }


// The configuration that wires sources to sinks
module MyFlowConfig implements DataFlow::ConfigSig {

  predicate isSource(DataFlow::Node source) {
    source instanceof PreprocessingSource
  }


  predicate isSink(DataFlow::Node sink) {
    // class-pollution: attacker controls the attribute *name* - 2nd arg
    exists(SetAttrSink call |
      sink = call.getArg(1)
    )
    // or
    // data-pollution: attacker controls the value being written - 3rd arg
    // exists(SetAttrSink call |
    //   sink = call.getArg(2)
    // )
  }


  predicate isAdditionalFlowStep(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
    fieldAssignFromParam(nodeFrom, nodeTo)
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
select source, "Dataflow to $@.", sink, sink.toString()