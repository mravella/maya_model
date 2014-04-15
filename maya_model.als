abstract sig Object {}

sig Node extends Object {
	attributes: set Attribute,
	connections: set Connection,
	id: one Id
}

sig Connection extends Object {
	connection: (Node->Attribute)->(Node->Attribute)
} {
	
}

sig Buffer {
	selection: set Object
}

sig Id {}
sig Type {}
sig Attribute {
	type: one Type
}

//model connection as (node->attribute)->(node-)


