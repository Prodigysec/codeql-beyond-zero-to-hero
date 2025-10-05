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

// DOESN'T MAKE SENSE
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
  }

}
module MyFlow = DataFlow::Global<MyFlowConfig>;

from MyFlow::PathNode source, MyFlow::PathNode sink
where MyFlow::flowPath(source, sink)
select source, "Dataflow to $@.", sink, sink.toString()