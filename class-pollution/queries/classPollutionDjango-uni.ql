/**
 * @name Django-Unicorn Class Pollution via set_property_value
 * @description Detects when property_name parameter flows through split() 
 *              and iteration to setattr, enabling class pollution
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @id py/django-unicorn-class-pollution
 */

import python
import semmle.python.dataflow.new.DataFlow
import DjangoUnicornFlow::PathGraph

/**
 * Source: property_name parameter in set_property_value function
 */
class PropertyNameSource extends DataFlow::ParameterNode {
  PropertyNameSource() {
    exists(Function f |
      f.getName() = "set_property_value" and
      this = DataFlow::parameterNode(f.getArgByName("property_name"))
    )
  }
}

/**
 * Sink: Second argument of setattr (attribute name)
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
 * Flow: property_name → property_name.split(".")
 */
predicate propertyNameToSplit(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(Call splitCall |
    splitCall.getFunc().(Attribute).getAttr() = "split" and
    nodeFrom = DataFlow::exprNode(splitCall.getFunc().(Attribute).getObject()) and
    nodeTo = DataFlow::exprNode(splitCall)
  )
}

/**
 * Flow: split() result → property_name_parts variable
 */
predicate splitToVariable(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(Assign assign, Call splitCall, Name varName |
    assign.getValue() = splitCall and
    assign.getATarget() = varName and
    splitCall.getFunc().(Attribute).getAttr() = "split" and
    nodeFrom = DataFlow::exprNode(splitCall) and
    nodeTo = DataFlow::exprNode(varName)
  )
}

/**
 * Flow: property_name_parts → for loop with enumerate
 * Handles: for idx, property_name_part in enumerate(property_name_parts):
 */
predicate listToEnumerateLoop(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(For f, Call enumerateCall, Name listVar, Tuple target |
    // enumerate(property_name_parts)
    enumerateCall.getFunc().(Name).getId() = "enumerate" and
    enumerateCall.getArg(0) = listVar and
    f.getIter() = enumerateCall and
    
    // for idx, property_name_part in ...
    target = f.getTarget() and
    
    // Flow from list variable to second element of tuple (the value, not index)
    nodeFrom = DataFlow::exprNode(listVar) and
    nodeTo = DataFlow::exprNode(target.getElt(1))
  )
}

/**
 * Flow: Direct list iteration without enumerate
 * Handles: for property_name_part in property_name_parts:
 */
predicate listToDirectLoop(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(For f, Name listVar |
    f.getIter() = listVar and
    nodeFrom = DataFlow::exprNode(listVar) and
    nodeTo = DataFlow::exprNode(f.getTarget())
  )
}

/**
 * Flow: Loop variable → setattr argument
 * Handles the case where property_name_part is used in setattr
 */
predicate loopVarToSetattr(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
  exists(Call setattrCall, Name loopVar |
    setattrCall.getFunc().(Name).getId() = "setattr" and
    setattrCall.getArg(1) = loopVar and
    nodeFrom = DataFlow::exprNode(loopVar) and
    nodeTo = DataFlow::exprNode(setattrCall.getArg(1))
  )
}

/**
 * Configuration for Django-Unicorn class pollution
 */
module DjangoUnicornConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    source instanceof PropertyNameSource
  }

  predicate isSink(DataFlow::Node sink) {
    sink instanceof SetAttrSink
  }

  predicate isAdditionalFlowStep(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
    propertyNameToSplit(nodeFrom, nodeTo)
    or
    splitToVariable(nodeFrom, nodeTo)
    or
    listToEnumerateLoop(nodeFrom, nodeTo)
    or
    listToDirectLoop(nodeFrom, nodeTo)
    or
    loopVarToSetattr(nodeFrom, nodeTo)
  }
}

module DjangoUnicornFlow = DataFlow::Global<DjangoUnicornConfig>;

from DjangoUnicornFlow::PathNode source, DjangoUnicornFlow::PathNode sink
where DjangoUnicornFlow::flowPath(source, sink)
select sink.getNode(), source, sink,
  "Class pollution: property_name parameter from $@ flows to setattr attribute name, allowing arbitrary attribute modification",
  source.getNode(), "set_property_value"