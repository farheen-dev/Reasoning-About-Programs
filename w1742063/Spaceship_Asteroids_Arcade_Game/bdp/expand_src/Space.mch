/* *******************************************************************************
** - 6SENG003C Reasoning About Programs Coursework (2020/21)
** - Machine: Space
** - Author: Mohamed Boosary Fathima Farheen
** - IIT No: 2018323
** - UOW No: w1742063
** - Creation date: 11/13/2021
******************************************************************************* */


MACHINE
    Space


CONCRETE_CONSTANTS
    regionX ,   // Range of x axis values Regions of Space
    regionY ,   // Range of y axis values Regions of Space
    gameRegion , // Regions belong to the Game Space
    homeBase ,  // Initial position of Spaceship
    starBase ,  // Docking position of Spaceship
    asteroids , // Space regions occupied by an asteroid
    spaceGrid   // Whole space including game space


PROPERTIES
    spaceGrid = POW ( NAT1 * NAT1 ) & // Defining spaceGrid
    regionX <: NAT1 &    // x axis values Regions is a subset of NAT1
    regionX = 1 .. 12 &  // Range of x axis values Regions of Space
    regionY <: NAT1 &    // x axis values Regions is a subset of NAT1
    regionY =  1 .. 7 &  // Range of x axis values Regions of Space
    gameRegion : spaceGrid &    // gameRegion is an element of spaceGrid
    gameRegion = regionX * regionY &    // initializing the gameRegion
    asteroids <: gameRegion &    // Asteroids is a subset of gameRegion
    asteroids = { ( 3 |-> 2 ) , ( 3 |-> 5 ) , ( 5 |-> 4 ) , ( 6 |-> 7 ) , ( 7 |-> 1 ) , ( 7 |-> 5 ) , ( 7 |-> 7 ) , ( 8 |-> 3 ) , ( 10 |-> 6 ) , ( 11 |-> 2 ) , ( 12 |-> 5 ) } & //  Positions of asteroids in the gameRegion
    homeBase : gameRegion &     // Homebase is a subset of gameRegion
    homeBase = ( 1 |-> 1 ) &    // Homebase position in the space spaceGrid
    starBase : gameRegion &    // Starbase is a subset of gameRegion
    starBase = ( 6 |-> 4 )    // Starbase position is a subset of gameRegion     
END
