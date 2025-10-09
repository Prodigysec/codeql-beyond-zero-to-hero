/**
 * @name Class pollution via dynamic attribute access
 * @description Detects when user-controlled data flows into getattr then setattr,
 *              allowing attackers to manipulate object attributes.
 * @kind path-problem
 * @id py/class-pollution
 * @problem.severity error
 * @precision high
 * Note: - This query tries to achieve a balance between a general model and precisely modeling the vulnerability
 *       - Uses TaintTracking to track taint-preserving operations. ie: If A is tainted, B is tainted if it's "derived from" A, even through transformations.
 *        Eg: x.split('.') -> the list elements are tainted if x is tainted
 * Result: Yields 1 TP
*/



import python
import semmle.python.dataflow.new.DataFlow
import semmle.python.dataflow.new.TaintTracking
import MyFlow::PathGraph

// Sources stay the same
class PreprocessingSource extends DataFlow::ParameterNode {
  PreprocessingSource() {
    exists(Function f |
      f.getName() = "__init__" and
      this = DataFlow::parameterNode(f.getArgByName("preprocessing"))
    )
  }
}

// Sinks stay the same
class SetAttrSink extends DataFlow::CallCfgNode {
  SetAttrSink() {
    exists(Call c |
      c.getFunc().(Name).getId() = "setattr" and
      this = DataFlow::exprNode(c)
    )
  }
}

// NOW: Keep only the field assignment step (structural flow)
// Remove itemsToLoopVars, fieldToItemsCall, fieldToAttr - taint tracking handles these!
predicate fieldAssignFromParam(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
    exists(PreprocessingSource p, Assign assign, Attribute lhs, Name rhs |
        assign.getValue() = rhs and
        assign.getATarget() = lhs and
        rhs.getId() = "preprocessing" and
        lhs.getAttr() = "_preprocessing" and
        lhs.getObject().(Name).getId() = "self" and
        nodeFrom = p and
        nodeTo = DataFlow::exprNode(lhs)
    )
}

predicate instanceAttributeFlow(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(Attribute write, Attribute read |
    write.getAttr() = "_preprocessing" and
    write.getObject().(Name).getId() = "self" and
    exists(Assign a | a.getATarget() = write) and
    
    read.getAttr() = "_preprocessing" and
    read.getObject().(Name).getId() = "self" and
    
    write.getScope().(Function).getEnclosingScope() = 
    read.getScope().(Function).getEnclosingScope() and
    
    nodeFrom = DataFlow::exprNode(write) and
    nodeTo = DataFlow::exprNode(read)
  )
}

// Switch to TaintTracking configuration
module MyFlowConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    source instanceof PreprocessingSource
  }

  predicate isSink(DataFlow::Node sink) {
    exists(SetAttrSink call |
      sink = call.getArg(1)  // Attribute name is controlled
    )
  }

  predicate isAdditionalFlowStep(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
    fieldAssignFromParam(nodeFrom, nodeTo)
    or
    instanceAttributeFlow(nodeFrom, nodeTo)
  }
}

// Use TaintTracking instead of DataFlow
module MyFlow = TaintTracking::Global<MyFlowConfig>;

from MyFlow::PathNode source, MyFlow::PathNode sink
where MyFlow::flowPath(source, sink)
select sink, "Class pollution: attacker-controlled attribute name from $@", 
       source, "user input"