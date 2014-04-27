open util/ordering[Time]

one sig Network {
	nodes: set Node -> Time
}

sig Time {}
sig Node {
	attributes: set Attribute,
	id: Id one -> Time
} {
	some attributes  // #sigfact
}
one sig Buffer {
	selection: set Node -> Time
}
sig Id {}
abstract sig Type {}
sig Float extends Type{}
sig Vector extends Type{}
sig Strng extends Type{}

sig Attribute {
	type:  Type one -> Time,
	value:  Value one -> Time,
	driving: set Attribute -> Time,
	driven:  Attribute lone -> Time
}
sig Value {}
sig DefaultValue extends Value {}  //All nodes will start with DefaultValue

//model connection as (node->attribute)->(node-)

run {} for 4

// Assert every Node has some attribute
assert nonEmptyAttributes {all n: Node | some a:Attribute | a in n.attributes}
check nonEmptyAttributes for 5 

//all x: Node.attributes.driving | 

fact connectionsMatchTypes {
	all t: Time | all a: Attribute | a.type.t = a.driven.t.type.t
}

fact invariants {
	all a: Attribute | all t: Time | a.type.t = a.type.(t.next) || t = last // Attribute types can't change
}

fact drivingMatchesDriven {
	all t: Time | all a, b: Attribute | a in b.driving.t iff b = a.driven.t 
}

pred init [t: Time] {
	all a: Attribute {
		a.value.t = DefaultValue
		no a.driven.t
		no a.driving.t
	}
}

/*
 * Preds:
 * MakeConnection
 * BreakConnection
 * DeleteNode 
 * CreateNode
 * Rename
 */

fact traces {
	init [first]
	all t: Time - last | let t' = t.next {
		some n: Node, a: Attribute, a': Attribute, i: Id |
			makeConnection[t, t', a, a']
			or breakConnection[t, t', a, a']
			or deleteNode[t, t', n]
			or createNode[t, t', n]
			or rename[t, t', n, i]
	}
}

pred rename[t, t': Time, n: Node, i: Id] {
	n.id.t' = i
	noNodeIdChangeExcept[t, t', n]
	noConnectionsChangeExcept[t, t', none]
	noNodesCreatedExcept[t, t', none]
	noNodesDestroyedExcept[t, t', none]
}

pred noNodeIdChangeExcept[t, t': Time, n: Node] {
	all n: Node-n | n.id.t = n.id.t'
}

pred noConnectionsChangeExcept[t, t': Time, a: Attribute] {
	all b: Attribute-a | 
		b.driven.t = b.driven.t' and
		b.driving.t = b.driving.t'
}

pred noNodesCreatedExcept[t, t': Time, n: Node] {
	Network.nodes.t = Network.nodes.t' ++ n
}

pred noNodesDestroyedExcept[t, t': Time, n: Node] {
	Network.nodes.t = Network.nodes.t' - n
}

