one sig Company {
stations: set ChargingStation, vehicles: set Vehicle
}
sig User {
ownedVehicles: set Vehicle, usedVehicle: lone Vehicle, disability: lone Disability
} {disability != none implies (usedVehicle & Scooter = none and usedVehicle & Bike = none)}
 sig Disability{}
sig ChargingStation { capacity: set Plug, chargingVehicles: Vehicle,
} {#chargingVehicles <= #capacity} sig Plug{}
abstract sig Vehicle {}
sig Car extends Vehicle{}
sig Scooter extends Vehicle{} sig Bike extends Vehicle{}
/* This is to guarantee the structural integrity of the model */ fact noTwoOwners {
no disjoint u1, u2: User | u1.ownedVehicles & u2.ownedVehicles != none and
no u: User | u.ownedVehicles & Company.vehicles != none }
fact noTwoUsersExploitingAVehicle {
no disjoint u1, u2: User | u1.usedVehicle = u2.usedVehicle
}

fact noChargingSameVehicleAtTwoStations {
no disjoint c1, c2: ChargingStation | c1.chargingVehicles & c2.chargingVehicles != none
}
fact noChargingVehicleInUse {
no c: ChargingStation, u: User | c.chargingVehicles & u.usedVehicle != none
}

assert existPeopleNotDisable{
lone u:User  | u.disability = none
}

pred compatibleVehicle[u: User, v: Vehicle]{
u.disability != none implies not (v in Scooter or v in Bike)
}
pred freeVehicle[v: Vehicle] {
all c: ChargingStation, u: User | not (v in c.chargingVehicles) and not (v in u.usedVehicle)
}
pred acquireVehicle[u: User, v: Vehicle, u': User] { compatibleVehicle[u, v] and
freeVehicle[v] and
u.usedVehicle = none
u'.ownedVehicles = u.ownedVehicles and u'.disability = u.disability and u'.usedVehicle = v
}
check existPeopleNotDisable
pred show(){} run show
run freeVehicle
run compatibleVehicle run acquireVehicle
