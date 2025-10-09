/**
 * @name Class pollution via dynamic attribute access
 * @description Detects when user-controlled data flows into getattr then setattr,
 *              allowing attackers to manipulate object attributes.
 * @kind path-problem
 * @id py/class-pollution
 * @problem.severity error
 * @precision low
 * Note: - This is a generalized query aimed at finding other variants of the CP vuln in docarray
 *       - Uses TaintTracking to track taint-preserving operations. ie: If A is tainted, B is tainted if it's "derived from" A, even through transformations.
 *        Eg: x.split('.') -> the list elements are tainted if x is tainted
 * Result: Yields 3 FP on docarray db
*/

import python
import semmle.python.dataflow.new.DataFlow
import semmle.python.dataflow.new.TaintTracking
import semmle.python.dataflow.new.RemoteFlowSources
import MyFlow::PathGraph

/**
 * Sources: User-controlled dictionaries or configuration objects
 */
class DictTypeSource extends DataFlow::ParameterNode {
  DictTypeSource() {
    exists(Parameter p |
      this = DataFlow::parameterNode(p) and
      (
        // Type annotations: dict, Dict, Dict[K,V], Mapping, etc.
        p.getAnnotation().(Name).getId() in ["dict", "Dict"]
        or
        exists(Subscript sub |
          p.getAnnotation() = sub and
          sub.getValue().(Name).getId() in ["Dict", "dict"]
        )
        or
        exists(Attribute attr |
          p.getAnnotation() = attr and
          attr.getAttr() in ["Dict", "Mapping", "MutableMapping"]
        )
        or
        exists(Subscript sub, Attribute attr |
          p.getAnnotation() = sub and
          sub.getValue() = attr and
          attr.getAttr() in ["Mapping", "MutableMapping"]
        )
      )
    )
  }
}

/**
 * Sinks: Dynamic attribute access operations
 */
class DynamicAttributeSink extends DataFlow::CallCfgNode {
  int argIndex;

  DynamicAttributeSink() {
    exists(Call c |
      this = DataFlow::exprNode(c) and
      (
        // setattr(obj, attr_name, value) - attr_name controlled
        (c.getFunc().(Name).getId() = "setattr" and argIndex = 1)
        or
        // getattr(obj, attr_name) - attr_name controlled
        (c.getFunc().(Name).getId() = "getattr" and argIndex = 1)
        or
        // delattr(obj, attr_name) - attr_name controlled
        (c.getFunc().(Name).getId() = "delattr" and argIndex = 1)
        or
        // hasattr(obj, attr_name) - attr_name controlled (timing attacks)
        (c.getFunc().(Name).getId() = "hasattr" and argIndex = 1)
        or
        // __setattr__(attr_name, value) - attr_name controlled
        (c.getFunc().(Attribute).getAttr() = "__setattr__" and argIndex = 0)
        or
        // __getattribute__(attr_name) - attr_name controlled
        (c.getFunc().(Attribute).getAttr() = "__getattribute__" and argIndex = 0)
      )
    )
  }
  
  int getVulnerableArgIndex() {
    result = argIndex
  }
}

/**
 * Interprocedural flow through instance attributes
 */
predicate instanceAttributeFlow(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(Attribute write, Attribute read, Class cls |
    // Write to self.attr or cls.attr
    write.getObject().(Name).getId() in ["self", "cls"] and
    exists(Assign a | a.getATarget() = write) and
    
    // Read from same attribute
    read.getAttr() = write.getAttr() and
    read.getObject().(Name).getId() = write.getObject().(Name).getId() and
    not exists(Assign a | a.getATarget() = read) and
    
    // Both in same class
    write.getScope().(Function).getScope() = cls and
    read.getScope().(Function).getScope() = cls and
    
    nodeFrom = DataFlow::exprNode(write) and
    nodeTo = DataFlow::exprNode(read)
  )
}

predicate isDunderCheckSanitized(DataFlow::Node node) {
  exists(For f, If ifStmt, Raise raiseStmt, Call methodCall |
    f.getIter() = node.asExpr() and
    ifStmt.getParentNode() = f and
    ifStmt.getTest().getASubExpression*() = methodCall and
    methodCall.getFunc().(Attribute).getAttr() in ["startswith", "endswith"] and
    methodCall.getArg(0).(StringLiteral).getText() = "__" and
    raiseStmt.getParentNode*() = ifStmt  // transitive closure(*)  check if the raise statement is anywhere within the if statement's body
  )
}


/**
 * Taint tracking configuration
 */
module MyFlowConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    source instanceof DictTypeSource
  }

  predicate isSink(DataFlow::Node sink) {
    exists(DynamicAttributeSink call |
      sink = call.getArg(call.getVulnerableArgIndex())
    )
  }

// include if you get false negative on exclusion
  predicate isAdditionalFlowStep(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
    // Cross-method instance attribute flow
    instanceAttributeFlow(nodeFrom, nodeTo)
  }
  
  predicate isBarrier(DataFlow::Node node) {
    isDunderCheckSanitized(node)
  }
}

module MyFlow = TaintTracking::Global<MyFlowConfig>;

from MyFlow::PathNode source, MyFlow::PathNode sink, DynamicAttributeSink sinkCall, Call c
where 
  MyFlow::flowPath(source, sink) and
  sink.getNode() = sinkCall.getArg(sinkCall.getVulnerableArgIndex()) and
  c = sinkCall.asExpr()
select sink.getNode(), source, sink,
  "Class pollution: attacker-controlled attribute name from $@ reaches " + 
  c.getFunc().toString(),
  source.getNode(), "user input"