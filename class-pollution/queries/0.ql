import python

from FunctionExpr fe
where fe.getLocation().getFile().getBaseName() = "torch_dataset.py"
select fe.getName()