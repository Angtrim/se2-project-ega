module myTaxiService

/*************** Classes ***************/


/** User **/
sig User {
    status: one UserStatus,
	requests : set Request
}

abstract sig UserStatus {}

lone sig ActiveUserStatus extends UserStatus {}
lone sig InactiveUserStatus extends UserStatus {}

/** Request **/
abstract sig RequestStatus{
}

lone sig ApprovedRequestStatus extends RequestStatus {}
lone sig RefuseRequestStatus extends RequestStatus {}

abstract sig Request{
	status: one RequestStatus,
	numOfPeople : one Int
}

sig ImmediateRequest extends Request{
}

sig ReservationRequest extends Request{
}

/** Ride **/




abstract sig Ride {
    driver: one TaxiDriver,
    passenger: some User
}

sig SingleRide extends Ride {} {#passenger = 1}
sig SharedRide extends Ride {} {#passenger > 1}

sig TaxiDriver {
    car: one Taxi,
    status: one TaxiStatus
}

sig TaxiZone {
    queue: one Queue
}

sig Taxi {
    seats: one Int
}

sig Queue {
    driver: set TaxiDriver
}

one sig QueueManager {
    queues: set Queue
}
/*************** RideManager ***************/

sig RideReqMap{
	ride : lone Ride,
	request : some Request
}

one sig RidesManager {
    qm: one QueueManager,
	ridesmap :  set RideReqMap
}




abstract sig TaxiStatus {}

lone sig TaxiBusy extends TaxiStatus {}
lone sig TaxiAvailable extends TaxiStatus {}

/*************** Facts ***************/

//there are enough seats to accommodate all the passengers 
fact allPassengersFit {
    all r: Ride | #r.passenger =< r.driver.car.seats
}

//each taxi has a maximum number of seats
fact maxTaxiSeats {
    all t: Taxi | quantityIsInBounds[t.seats]
}

//there exists at least one passenger per ride
fact rideHasReasonToExist {
    no r: SingleRide | #r.passenger < 1
}

//there exists at least one driver per taxi 
fact taxiCarHasReasonToExist {
    all t: Taxi | one d: TaxiDriver | t in d.car
}

//two different rides can't have the same user
fact userHasOneRide {
    all u: User | lone r: Ride | u in r.passenger
}

//two different queues can't have the same taxi driver
fact uniqueQueueForDriver {
    all d: TaxiDriver | lone q: Queue | d in q.driver
}

//two different taxi drivers can't have the same car
fact uniqueTaxi{
    all t: Taxi | lone d: TaxiDriver | t in d.car
}

//two rides can't have the same driver
fact uniqueDrive {
    all d: TaxiDriver | lone r: Ride | d in r.driver
}

//if the driver is available he is not in a ride
fact availability {
    all d: TaxiDriver | isAvailable[d]  implies !( isInRide[d] )  
}

//if the user is active he is in a ride
fact activity {
    all u: User | isActive[u]  iff ( isUserInRide[u] )  
}

//if the driver is available he is in a queue
fact availabilityInQueue {
    all d: TaxiDriver | isAvailable[d] implies !( isNotInQueue[d] )  
}

//if the driver is in a ride then the status is busy 
fact unavailability {
    all d: TaxiDriver | isInRide[d] implies isBusy[d]
}

//if the driver is busy, he is not in a queue
fact noBusyDriverBelongsToQueue {
    all d: TaxiDriver | isBusy[d]  implies isNotInQueue[d]
} 

//all queues belong to the QueueManager
fact allQueuesBelongToQueueManager {
    all q: Queue | one qm: QueueManager | q in qm.queues
}

//two zones cannot have the same queue 
fact oneZoneOneQueue {
    all q: Queue | one z: TaxiZone | q in z.*queue
}



//all rides belong to the RideManager
fact allRidesBelongToRideManager {
  // all r: Ride | one rm: RidesManager | r in rm.rides
}

// num of people in request is in bound
fact numOfPeopleInBound{
	all r: Request |quantityIsInBounds [r.numOfPeople]
}

// for every request must exist exctly one map with a ride associated
fact aMapForEveryRequest{

//	all r: Request | one m : RideReqMap |one rd : Ride | m.request = r && m.ride = rd

}

//two different maps cant have the same ride
fact uniqueRideForMap{
    all r: Ride | one m: RideReqMap | r in m.ride
}


// for every request there is one user
fact uniqueRequestForMap{
	all rq:Request | one u: User |rq in u.requests
}

// for every request there is at most one map
fact uniqueRequestForMap{
	all rq:Request | lone m: RideReqMap |rq in m.request
}

// if the req is approved there is exactly one map
fact mapForApproved{
	all rq:Request |  isApprovedRequest[rq] implies one m: RideReqMap | rq in m.request
}

// if the req is  not approved there is exactly zero map
fact mapForRefused{
	all rq:Request |  !isApprovedRequest[rq] implies no m: RideReqMap | rq in m.request
}


//two different maps cant have the same req
fact uniqueRequestForMap{
    all rq: Request |  one m: RideReqMap | isApprovedRequest[rq] iff rq in m.request
}

//all maps belong to ridemanager
fact allMapToRideManager{
	all m : RideReqMap | one mn: RidesManager | m in mn.ridesmap
}


// a request and a ride are connected iff the have the same user
fact userInRideAndInRequest{
//	all rq: Request | all rd: Ride | areConnected[rd,rq] iff rd.passenger = userOfRequest[rq]
//all rq: Request | all rd: Ride | areConnected[rd,rq] iff haveSameUser[rd,rq]
}

// if the map has a single ride the map has only one request
fact oneRequestInMapForSingleRide{
	all m: RideReqMap | m.ride in SingleRide implies #m.request = 1
}

// if the map has a single ride the map has only one request
fact correctRequestInMapForSharedRide{
	all m: RideReqMap | m.ride in SharedRide implies #m.request = #m.ride.passenger
}

fact passengerNumberCorrect {
	all m: RideReqMap | m.ride.driver.car.seats >= sum m.request.numOfPeople
}


/*************** Functions ***************/

fun numberOfSeats [r: Ride]: Int {
    r.driver.car.seats
}

fun userOfRequest[rq:Request]:  User{
  { u: User | rq in u.requests }  
}


/*************** Assertions ***************/




/*************** Predicates ***************/

pred haveSameUser[rd:Ride,rq:Request]{

all u1 : User | one u2: User |  u1 in rd.passenger && u2 = u1 &&  rq in u2.requests

}




pred isAvailable [ d: TaxiDriver ] {
    some s: TaxiAvailable | d.status in s
}

pred isActive [ u: User ] {
    some s: ActiveUserStatus | u.status in s
}

pred isBusy [ d: TaxiDriver ] {
    some s: TaxiBusy | d.status in s
}

pred isInactive [ u: User ] {
    some s: InactiveUserStatus | u.status in s
}

pred isInRide [ d: TaxiDriver ] {
    some r:Ride | d in r.driver
}

pred isUserInRide [ u: User ] {
    some r:Ride | u in r.passenger
}

pred isNotInQueue[ d: TaxiDriver]{
    no q:Queue | d in q.driver
}

pred quantityIsInBounds [n: Int] {
    n > 1 && n < 6
}

pred isApprovedRequest[r:Request]{
	one s: ApprovedRequestStatus | r.status in s
}

pred areConnected[rd:Ride,rq: Request]{

	one m : RideReqMap | rd = m.ride && rq = m.request

}



pred show {


	#User = 2
}

run show for 10
