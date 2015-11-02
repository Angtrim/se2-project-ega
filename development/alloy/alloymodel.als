module myTaxiService

/* class declaration */


sig GenericText {}

sig User {
	ID: one GenericText,
}

sig Ride {
	passenger: some User,
	driver: one TaxiDriver
}

sig TaxiDriver {
	ID: one GenericText,
	license: one GenericText,
	car: one Taxi,
	//status: one TaxiStatus
}

/*
sig TaxiStatus {
	code: one Int
} {	code >= 0
	code <= 5}
*/
sig Taxi {
	seats: one Int,
	plate: one GenericText
}


sig Queue {
	driver: some TaxiDriver,
}
/*
sig QueueManager {
	queues: some Queue
}

//facts

fact allPassengersFit {
	no r: Ride | #r.passenger > r.driver.car.seats
}

//each taxi has a maximum number of seats
fact maxTaxiSeats {
	no t: Taxi | t.seats < 1
	no t: Taxi | t.seats > 6
}

//there exists at least one passenger per ride
fact rideHasReasonToExist {
	no r: Ride | #r.passenger < 1
}

//two different rides can't have the same user
*/
fact userHasOneRide {
	all u: User | lone r: Ride | u in r.passenger
}


//A single taxi driver cant't belong to two different queues
fact uniqueQueue {
	all t: TaxiDriver | lone q: Queue | t in q.driver
}
/*
//there is only one queue manager
fact oneQueueManager {

}
*/
//run
pred show {

}

run show for 1 but 4 User, 3 Ride, 3 TaxiDriver, 4 Queue