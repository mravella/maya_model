open util/ordering[Time]

one sig Network {
	nodes: set Node -> Time
} 

sig Time {}
sig Node {
	attributes: set Attribute  -> Time,
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

run {} for 3
/*fact someNodeInNetwork { //delete this later
	some disj n, n':Node | n+n' in Network.nodes.first
}*/ //why doesn't this work


fact noSharedId {  --NEW
	all t: Time | all n, n': Network.nodes.t | n.id.t = n'.id.t implies n = n'
}

fact connectionsMatchTypes {
	all t: Time | all a: Attribute | some a.driven.t implies a.type.t = a.driven.t.type.t
}

fact attributeTypesCantChange {
	all a: Attribute | all t: Time | a.type.t = a.type.(t.next) || t = last 
}

fact drivingMatchesDriven {
	all t: Time | all a, b: Attribute | a in b.driving.t iff b = a.driven.t 
}

//No attribute drives itself
fact noAttributeDrivesItself {
	all a, a': Attribute | all t: Time | a.driven.t = a' implies a != a'
}

fact attributesStayTheSame {
	all t, t': Time | all n: Node | n.attributes.t = n.attributes.t'
}

//Attributes can only belong to one node
fact oneNodePerAttribute {
	all t: Time | all a: Attribute | some n: Node | a in n.attributes.t
	all disj n, n': Node | all t: Time | no n.attributes.t & n'.attributes.t
}

//Attributes cant be driven and have default value
fact noNodesDrivenAndDefault {
	all t: Time | no a: Attribute | some a.driven.t and a.value.t = DefaultValue
}

//Node driving does what node driving should do
fact driving {
	all a, a': Attribute | all t: Time | a' in a.driving.t implies a'.value.t = a.value.t
}

fact nodesNotInNetworkAreSterile {
	all t: Time | all n: Node | n not in Network.nodes.t implies no n.attributes.t.driven.t and no n.attributes.t.driving.t
} //check nodesNotInNetworkAreSterile for 3

/*
 * Preds:
 * MakeConnection
 * BreakConnection
 * DeleteNode 
 * CreateNode
 * Rename
 */


fact traces {
	all t: Time - last | let t' = t.next {
		some n: Node, disj a, a': Attribute, i: Id |
			makeConnection[t, t', a, a']
			or breakConnection[t, t', a, a']
			or deleteNode[t, t', n]
			or createNode[t, t', n]
			or rename[t, t', n, i]
	}
}

pred rename[t, t': Time, n: Node, i: Id] {
	n.id.t' = i
	n.id.t not = n.id.t'
	noNodeIdChangeExcept[t, t', n]
	noConnectionsChangeExcept[t, t', none]
	noNodesCreatedExcept[t, t', none]
	noNodesDestroyedExcept[t, t', none]
}

pred noNodeIdChangeExcept[t, t': Time, n: Node] {
	all n': Network.nodes.t - n | n'.id.t = n'.id.t'
}

/*
Changed this to take in a set so we can include both attributes
*/
pred noConnectionsChangeExcept[t, t': Time, a: set Attribute] {
	all b: Attribute-a | 
		b.driven.t = b.driven.t' and
		b.driving.t = b.driving.t'
}

pred noNodesCreatedExcept[t, t': Time, n: Node] { //can only create one at a time
	Network.nodes.t' = Network.nodes.t + n
}

pred noNodesDestroyedExcept[t, t': Time, n: set Node] { //can delete multiple at time=>set Node
	Network.nodes.t' = Network.nodes.t - n
}

pred createNode[t, t': Time, n: Node] {
	n not in Network.nodes.t
	Network.nodes.t' = Network.nodes.t + n
	noConnectionsChangeExcept[t, t', none]
	noNodeIdChangeExcept[t, t', none]
}

pred deleteNode[t, t': Time, n: set Node] {
	n in Network.nodes.t
	Network.nodes.t' = Network.nodes.t - n
	noNodesDestroyedExcept[t, t', n]
	noConnectionsChangeExcept[t, t', none]
	noNodeIdChangeExcept[t, t', none]
}

pred breakConnection[t, t': Time, a, a': Attribute] {
	a' in a.driving.t
	a in a'.driven.t
	a.driving.t' = a.driving.t - a'
	a'.driven.t' = none
	a'.value.t' = DefaultValue
	noNodesCreatedExcept[t, t', none]
	noNodesDestroyedExcept[t, t', none]
	noConnectionsChangeExcept[t, t', a + a']
	noNodeIdChangeExcept[t, t', none]
}

pred makeConnection[t, t': Time, a, a': Attribute] {
	a' not in a.driving.t
	a not in a'.driven.t
	a.driving.t' = a.driving.t + a'
	a'.driven.t.driving.t' = a'.driven.t.driving.t - a'  --wow
	a'.driven.t' = a
	noNodesCreatedExcept[t, t', none]
	noNodesDestroyedExcept[t, t', none]
	noConnectionsChangeExcept[t, t', a + a']
	noNodeIdChangeExcept[t, t', none]
}


//UI Preds
pred UIDelete[t, t': Time]{ //deletes whatever you have selected
	deleteNode[t, t', Buffer.selection.t]
}



// Checks every Node has some attribute
assert nonEmptyAttributes {
	all t: Time | all n: Node | some a:Attribute | a in n.attributes.t
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

//Attributes only belong to one node
assert oneNodePerAttribute {
	all t: Time | all disj n, n': Node | no a: Attribute | a in n.attributes.t and a in n'.attributes.t
} check oneNodePerAttribute for 2  --Oh wow!  Much flaw.

//Nodes attribute sets don't change
assert attributesDontChangeOverTime {
	all t, t': Time | all n: Node | n.attributes.t = n.attributes.t'
} check attributesDontChangeOverTime for 2

//Nodes cant be driven by another node and have the default value
assert nodesCantBeDefaultValueAndDriven {
	all a: Attribute | all t: Time | some a.driven.t implies a.value.t != DefaultValue
} check nodesCantBeDefaultValueAndDriven for 5

//Driving nodes actually drives nodes
assert drivenHasSameValueAsDriving {
	all t: Time | all a, a': Attribute | a.driven.t = a' implies a.value.t = a'.value.t
} check drivenHasSameValueAsDriving for 3

assert nodesNeedNotBeDriving { //problem b/c everything seems to need to be driven/driving
	all t: Time | all a: Attribute | some a.driving.t or some a.driven.t
} check nodesNeedNotBeDriving for 3
