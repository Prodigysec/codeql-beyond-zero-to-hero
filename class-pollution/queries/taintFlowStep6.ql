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

        nodeFrom = p and
        nodeTo   = DataFlow::exprNode(lhs)
    )
}

predicate fieldToItemsCall(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(Call itemsCall, Attribute funcAttr, Attribute recvAttr |
    // the function being called is `.items`
    itemsCall.getFunc() = funcAttr and
    funcAttr.getAttr() = "items" and

    // receiver of `.items` is an attribute access
    funcAttr.getObject() = recvAttr and
    recvAttr.getAttr() = "_preprocessing" and

    // receiver of `_preprocessing` is exactly `self`
    recvAttr.getObject().(Name).getId() = "self" and

    // map into dataflow nodes
    nodeFrom = DataFlow::exprNode(recvAttr) and
    nodeTo   = DataFlow::exprNode(itemsCall)
  )
}

predicate itemsToLoopVars(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(For f, Call itemsCall, Attribute recv |
    f.getIter() = itemsCall and
    itemsCall.getFunc().(Attribute).getAttr() = "items" and

    // constrain to self._preprocessing.items()
    recv = itemsCall.getFunc().(Attribute).getObject() and
    recv.getAttr() = "_preprocessing" and
    recv.getObject().(Name).getId() = "self" and

    nodeFrom = DataFlow::exprNode(itemsCall) and
    nodeTo   = DataFlow::exprNode(f.getTarget())
  )
}

predicate callThroughCallable(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(Call c, Name fn |
    c.getFunc() = fn and
    fn.getId() = "preprocess" and
    (
      // Flow from callable to return value
      nodeFrom = DataFlow::exprNode(fn) and
      nodeTo = DataFlow::exprNode(c)
    )
  )
}


/**
 * Flow step: field string → attr (via split + subscript).
 * string transformation step
 */
predicate fieldToAttr(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(
    Call splitCall, Assign accPathAssign, Name accPathDef,
    Assign attrAssign, Name attr, Name accPathUse,
    Subscript sub, UnaryExpr unary, IntegerLiteral lit
  |
    // acc_path = field.split('.')
    accPathAssign.getValue() = splitCall and
    accPathAssign.getATarget() = accPathDef and
    splitCall.getFunc().(Attribute).getAttr() = "split" and
    // source = field in field.split('.')
    nodeFrom = DataFlow::exprNode(splitCall.getFunc().(Attribute).getObject()) and
    
    // attr = acc_path[-1]
    attrAssign.getValue() = sub and
    attrAssign.getATarget() = attr and
    sub.getObject() = accPathUse and
    // index = -1 → UnaryExpr(USub, IntegerLiteral(1))
    sub.getIndex() = unary and
    unary.getOp() instanceof USub and
    unary.getOperand() = lit and
    lit.getValue() = 1 and
    
    // Ensure acc_path in both places refers to the same variable
    accPathDef.getId() = accPathUse.getId() and
    
    // flow into the attr variable (the target of the assignment)
    nodeTo = DataFlow::exprNode(attr)
  )
}


/**
 * Models flow of attribute names into setattr (class pollution sink).
 * Connects the variable `attr` (derived from field) to the second argument of `setattr`.
 */
predicate flowThroughAttributeAccess(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(Call c, Name fn, Expr attrArg |
    c.getFunc() = fn and
    fn.getId() = "setattr" and

    // second argument (the attribute name)
    c.getArg(1) = attrArg and
    attrArg.(Name).getId() = "attr" and

    // source: the variable `attr`
    nodeFrom = DataFlow::exprNode(attrArg) and

    // sink: the argument slot itself (not just the same variable node)
    nodeTo = DataFlow::exprNode(c.getArg(1))
  )
}





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
    or
    // data-pollution: attacker controls the value being written - 3rd arg
    exists(SetAttrSink call |
      sink = call.getArg(2)
    )
  }


  predicate isAdditionalFlowStep(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
    fieldAssignFromParam(nodeFrom, nodeTo)
    or
    fieldToItemsCall(nodeFrom, nodeTo)
    or

    
    itemsToLoopVars(nodeFrom, nodeTo)
    or 
    callThroughCallable(nodeFrom, nodeTo)
    or
    fieldToAttr(nodeFrom, nodeTo)
    or
    flowThroughAttributeAccess(nodeFrom, nodeTo)
  }

}
module MyFlow = DataFlow::Global<MyFlowConfig>;

from MyFlow::PathNode source, MyFlow::PathNode sink
where MyFlow::flowPath(source, sink)
select source, "Dataflow to $@.", sink, sink.toString()