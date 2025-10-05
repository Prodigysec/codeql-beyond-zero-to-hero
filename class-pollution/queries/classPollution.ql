/**
 * @name Class Pollution via setattr
 * @description Detects when attacker-controlled data flows into the attribute name
 *              parameter of setattr, enabling class pollution attacks
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @id py/class-pollution-setattr
 * @tags security
 *       external/cwe/cwe-915
 */

import python
import semmle.python.dataflow.new.DataFlow
import GeneralClassPollutionFlow::PathGraph

/**
 * Sources: Parameters and inputs that could contain attacker-controlled data
 */
class UntrustedSource extends DataFlow::Node {
  UntrustedSource() {
    // Function parameters with suspicious names
    exists(Parameter p |
      p.getName() in [
        "request", "data", "params", "properties", "updates", "payload",
        "preprocessing", "property_name", "path", "field", "key", "name"
      ] and
      this = DataFlow::parameterNode(p)
    )
    or
    // Dictionary-typed parameters
    exists(Parameter p |
      p.getAnnotation().toString().matches("%Dict%") and
      this = DataFlow::parameterNode(p)
    )
    or
    // HTTP framework request objects
    exists(Attribute a |
      (
        a.getAttr() in ["POST", "GET", "data", "json", "form"] or
        a.toString().matches("request.%")
      ) and
      this = DataFlow::exprNode(a)
    )
  }
}

/**
 * Sinks: The attribute name argument (2nd arg) of setattr calls
 */
class SetAttrSink extends DataFlow::Node {
  SetAttrSink() {
    exists(Call c |
      c.getFunc().(Name).getId() = "setattr" and
      this = DataFlow::exprNode(c.getArg(1))
    )
  }
}

/**
 * Flow through dictionary iteration patterns
 */
predicate dictionaryIteration(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(Call c, For f |
    c.getFunc().(Attribute).getAttr() in ["items", "keys", "values"] and
    f.getIter() = c and
    nodeFrom = DataFlow::exprNode(c) and
    (
      // Tuple unpacking: for key, value in dict.items()
      nodeTo = DataFlow::exprNode(f.getTarget().(Tuple).getElt(0))
      or
      // Direct: for key in dict.keys()
      nodeTo = DataFlow::exprNode(f.getTarget())
    )
  )
}

/**
 * Flow through string transformations
 */
predicate stringTransformation(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(Call c |
    // String methods: split, strip, replace, etc.
    c.getFunc().(Attribute).getAttr() in [
      "split", "strip", "lstrip", "rstrip", 
      "replace", "lower", "upper", "removeprefix", "removesuffix"
    ] and
    nodeFrom = DataFlow::exprNode(c.getFunc().(Attribute).getObject()) and
    nodeTo = DataFlow::exprNode(c)
  )
  or
  exists(Subscript sub |
    // Subscript: path[-1], parts[0], etc.
    nodeFrom = DataFlow::exprNode(sub.getObject()) and
    nodeTo = DataFlow::exprNode(sub)
  )
}

/**
 * Interprocedural flow through instance attributes
 */
predicate attributeStoreLoad(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
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

/**
 * Flow through method call receivers to call results
 */
predicate callReceiverToResult(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(Call c, Attribute recv |
    c.getFunc() = recv and
    nodeFrom = DataFlow::exprNode(recv.getObject()) and
    nodeTo = DataFlow::exprNode(c)
  )
}

/**
 * Configuration for class pollution detection
 */
module GeneralClassPollutionConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    source instanceof UntrustedSource
  }

  predicate isSink(DataFlow::Node sink) {
    sink instanceof SetAttrSink
  }

  predicate isAdditionalFlowStep(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
    dictionaryIteration(nodeFrom, nodeTo)
    or
    stringTransformation(nodeFrom, nodeTo)
    or
    attributeStoreLoad(nodeFrom, nodeTo)
    or
    callReceiverToResult(nodeFrom, nodeTo)
  }
  
  predicate isBarrier(DataFlow::Node node) {
    // Stop flow if validated against whitelist
    exists(Compare cmp |
      cmp.getASubExpression() = node.asExpr() and
      cmp.getOp(0) instanceof In and
      exists(List l | l = cmp.getASubExpression())
    )
    or
    // Stop flow if explicitly validated
    exists(Call c |
      c.getFunc().(Name).getId() in [
        "validate", "sanitize", "check_allowed", 
        "verify", "is_valid", "is_safe"
      ] and
      c.getAnArg() = node.asExpr()
    )
  }
}

module GeneralClassPollutionFlow = DataFlow::Global<GeneralClassPollutionConfig>;

from GeneralClassPollutionFlow::PathNode source, GeneralClassPollutionFlow::PathNode sink
where GeneralClassPollutionFlow::flowPath(source, sink)
select sink.getNode(), source, sink,
  "Class pollution: attacker-controlled data from $@ flows to setattr attribute name",
  source.getNode(), source.getNode().toString()