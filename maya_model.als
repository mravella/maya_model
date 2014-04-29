open util/ordering[Time]

one sig Network {
	nodes: set Node -> Time
} {
	all n: Node | all t: Time | n in nodes.t --All nodes are in the network.  This isn't right, but I don't really know what to do.
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
one sig DefaultValue extends Value {}  //All nodes will start with DefaultValue

//model connection as (node->attribute)->(node-)

run {} 

//all x: Node.attributes.driving | 

fact noSharedId {  --NEW
	all n, n': Node | all t: Time | n.id.t = n'.id.t implies n = n'
}

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

/*
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
}*/

pred rename[t, t': Time, n: Node, i: Id] {
	n.id.t' = i
	noNodeIdChangeExcept[t, t', n]
	noConnectionsChangeExcept[t, t', none]
	noNodesCreatedExcept[t, t', none]
	noNodesDestroyedExcept[t, t', none]
}

pred noNodeIdChangeExcept[t, t': Time, n: Node] {
	all n1: Node-n | n1.id.t = n1.id.t'
}

/*
Changed this to take in a set so we can include both attributes
*/
pred noConnectionsChangeExcept[t, t': Time, a: set Attribute] {
	all b: Attribute-a | 
		b.driven.t = b.driven.t' and
		b.driving.t = b.driving.t'
}

pred noNodesCreatedExcept[t, t': Time, n: Node] {
	Network.nodes.t = Network.nodes.t' ++ n
}

pred noNodesDestroyedExcept[t, t': Time, n: Node] {
	Network.nodes.t' = Network.nodes.t - n
}

pred createNode[t, t': Time, n: Node] {
	Network.nodes.t' = Network.nodes.t ++ n
	noNodesCreatedExcept[t, t', n]
	noConnectionsChangeExcept[t, t', none]
	noNodeIdChangeExcept[t, t', none]
}

pred deleteNode[t, t': Time, n: Node] {
	Network.nodes.t' = Network.nodes.t - n
	noNodesDestroyedExcept[t, t', n]
	noConnectionsChangeExcept[t, t', none]
	noNodeIdChangeExcept[t, t', none]
}

pred breakConnection[t, t': Time, a, a': Attribute] {
	a.driving.t' = a.driving.t - a'
	a'.driven.t' = none
	a'.value.t' = DefaultValue
	noNodesCreatedExcept[t, t', none]
	noNodesDestroyedExcept[t, t', none]
	noConnectionsChangeExcept[t, t', a + a']
	noNodeIdChangeExcept[t, t', none]
}

pred makeConnection[t, t': Time, a, a': Attribute] {
	a.driving.t' = a.driving.t ++ a'
	a'.driven.t'.driving.t' = a'.driven.t.driving.t - a'  --wow
	a'.driven.t' = a
	noNodesCreatedExcept[t, t', none]
	noNodesDestroyedExcept[t, t', none]
	noConnectionsChangeExcept[t, t', a + a']
	noNodeIdChangeExcept[t, t', none]
}
	

// Checks every Node has some attribute
assert nonEmptyAttributes {
	all n: Node | some a:Attribute | a in n.attributes
} check nonEmptyAttributes for 5 

// Checks that types of attributes don't change over time
assert noTypeChange {
	all a: Attribute | all t, t': Time | a.type.t = a.type.t'
} check noTypeChange for 5

// Driven values share type
assert drivingTypeCheck {
	all a, a': Attribute | all t: Time | a'.driven.t = a implies a.type.t = a'.type.t
} check drivingTypeCheck for 5

//No nodes share an ID
assert noSharedIds {
	all n, n': Node | all t: Time | (n.id.t = n'.id.t) implies n = n'
} check noSharedIds for 5



