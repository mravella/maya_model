open util/ordering[Time]

run {} for 3 but 10 Time

one sig Network {
	nodes: set Node -> Time
} 

sig Time {}
sig Node {
	attributes: set Attribute  -> Time,
	id: Id one -> Time
} {
	some attributes 
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

fact noSharedId {  
	all t: Time | all n, n': Node | n.id.t = n'.id.t implies n = n'
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

//Enforces that node driving causes a change to values
fact driving {
	all a, a': Attribute | all t: Time | a' in a.driving.t implies a'.value.t = a.value.t
}

fact nodesNotInNetworkAreSterile {
	all t: Time | all n: Node | n not in Network.nodes.t implies no n.attributes.t.driven.t and no n.attributes.t.driving.t
} //check nodesNotInNetworkAreSterile for 3

//Buffer initializes to empty
fact bufferInitiallyEmpty {
	no Buffer.selection.first
} 

//Buffer can only select nodes on screen
fact bufferInNetwork {
	all t: Time | Buffer.selection.t in Network.nodes.t
}

//Cycles cause all nodes in cycle to have same value
fact cyclicAttributesLocks {
	all t: Time | all a: Attribute | a in a.^(driving.t) implies a.value.t = a.value.(t.next)
}  

fact traces { //Each time step must take one of these actions
	all t: Time - last | let t' = t.next {
		some n: set Node, disj a, a': Attribute, i: Id |
			makeConnection[t, t', a, a']
		    or breakConnection[t, t', a, a']
			or createNode[t, t', n]
			or rename[t, t', n, i]
			or UIDelete[t,t']
			or UIOverwriteSelection[t, t', n]
			or UIToggleSelection[t,t',n]
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
pred rename[t, t': Time, n: set Node, i: Id] {
	#n = 1 //so that you can only rename one node at once
	n.id.t' = i
	n.id.t not = n.id.t'
	noNodeIdChangeExcept[t, t', n]
	noConnectionsChangeExcept[t, t', none]
	noNodesCreatedExcept[t, t', none]
	noNodesDestroyedExcept[t, t', none]
}

pred createNode[t, t': Time, n: set Node] {
	#n = 1
	n not in Network.nodes.t
	Network.nodes.t' = Network.nodes.t + n
	noConnectionsChangeExcept[t, t', none]
	noNodeIdChangeExcept[t, t', none]
	noValueChangeExcept[t, t', none]
	noBufferChange[t, t']
}

pred deleteNode[t, t': Time, n: set Node] {
	Network.nodes.t' = Network.nodes.t - n
	all v: n.attributes.t.driving.t.value.t' | v = DefaultValue
	noNodesDestroyedExcept[t, t', n]
	noConnectionsChangeExcept[t, t', none]
	noNodeIdChangeExcept[t, t', none]
	noValueChangeExcept[t, t', n.attributes.t + n.attributes.t.driving.t]
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
	noValueChangeExcept[t, t', a']
	noBufferChange[t, t']
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
	noValueChangeExcept[t, t', a']
	noBufferChange[t, t']
}

//UI Preds
pred UIOverwriteSelection[t, t': Time, n: set Node]{ //replaces old buffer with new selection
	Buffer.selection.t' != Buffer.selection.t
	Buffer.selection.t' = n
	networkInvariance[t, t']	//nothing changes but buffer
}

pred UIToggleSelection[t, t': Time, n: set Node]{//toggles selected nodes
	Buffer.selection.t' != Buffer.selection.t
	all node: n | node in Buffer.selection.t implies node not in Buffer.selection.t' and
						node not in Buffer.selection.t implies node in Buffer.selection.t'
	networkInvariance[t, t']
}

pred UIDelete[t, t': Time]{ //deletes whatever you have selected using selection preds
	some Buffer.selection.t
	deleteNode[t, t', Buffer.selection.t]
	no Buffer.selection.t'
}

/*
Invariants section
*/
pred noNodeIdChangeExcept[t, t': Time, n: Node] {
	all n': Network.nodes.t - n | n'.id.t = n'.id.t'
}

//takes in a set so we can include both attributes
pred noConnectionsChangeExcept[t, t': Time, a: set Attribute] {
	all b: Attribute - a | 
		b.driven.t = b.driven.t' and
		b.driving.t = b.driving.t'
}

pred noNodesCreatedExcept[t, t': Time, n: Node] { //can only create one at a time
	Network.nodes.t' = Network.nodes.t + n
}

pred noNodesDestroyedExcept[t, t': Time, n: set Node] { //can delete multiple at time=>set Node
	Network.nodes.t' = Network.nodes.t - n
}

pred noValueChangeExcept[t, t': Time, a: set Attribute] {
	all b: Attribute - a | b.value.t = b.value.t' 
}

//nothing changes in the network. used for changes to buffer
pred networkInvariance[t,t': Time]{ 
	noNodesCreatedExcept[t, t', none]
	noNodesDestroyedExcept[t, t', none]
	noConnectionsChangeExcept[t, t', none]
	noNodeIdChangeExcept[t, t', none]
	noValueChangeExcept[t, t', none]
}

//used for network changes on attributes and node creation
pred noBufferChange[t, t': Time] { 
	Buffer.selection.t = Buffer.selection.t'
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

//Buffer can only select things in the network
assert bufferOnlyInNetwork { 
	all t: Time | all n: Node | n in Buffer.selection.t implies n in Network.nodes.t
} check bufferOnlyInNetwork for 5

//Used to make show example with multiple nodes in the buffer (should find counter examples)
assert bufferCanHazMoreThanOneNode {
	all t: Time | #Buffer.selection.t <= 1
} check bufferCanHazMoreThanOneNode for 5

assert bufferEmptyAfterDelete {
	all t: Time | UIDelete[t, t.next] implies no Buffer.selection.(t.next)
} check bufferEmptyAfterDelete for 5

assert deletionCausesDefaultValue {
	all t: Time | UIDelete[t, t.next] implies Buffer.selection.t.driving.t.value.(t.next) = DefaultValue
} check deletionCausesDefaultValue for 5

assert noDefaultDriver {
	all t, t': Time | all a, a' :Attribute | makeConnection[t,t',a,a'] => a.value.t !=DefaultValue
//not (a.value.t = DefaultValue and makeConnection[t,t',a,a']) //2 ways to say same thing
} check noDefaultDriver
