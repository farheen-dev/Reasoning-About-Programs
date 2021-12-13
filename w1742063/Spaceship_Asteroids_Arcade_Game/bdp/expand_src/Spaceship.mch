/* *******************************************************************************
** - 6SENG003C Reasoning About Programs Coursework (2020/21)
** - Machine: Spaceship
** - Author: Mohamed Boosary Fathima Farheen
** - IIT No: 2018323
** - UOW No: w1742063
** - Creation date: 11/13/2021
******************************************************************************* */


MACHINE
    Spaceship


SEES
    Space


SETS
    NORMAL_MOVEMENT_REPORT = { SUCCESSFUL_MOVEMENT , MOVEMENT_FAILED_INSUFFICIENT_POWER , MOVEMENT_FAILED_HIT_ASTEROID ,
                              MOVEMENT_FAILED_REGION_OUT_OF_BOUND , GAME_OVER_START_NEW_GAME , MOVEMENT_IMPOSSIBLE_PLEASE_START_THE_GAME } ;

    WARP_DRIVE_REPORT = { SUCCESSFUL_WARP_DRIVE , WARP_DRIVE_FAILED_INSUFFICIENT_POWER , CANNOT_WARP_DRIVE_INTO_ASTEROID ,
                         WARP_DRIVE_FAILED_REGION_OUT_OF_BOUND , CANNOT_WARP_INTO_STARBASE_FROM_HOMEBASE ,
                         WARP_DRIVE_GAME_OVER_START_NEW_GAME , WARP_DRIVE_IMPOSSIBLE_PLEASE_START_THE_GAME ,
                         CANNOT_WARP_INTO_SAME_REGION } ;

    GAME_STATUS = { GAME_NOT_STARTED , START_THE_GAME , RESTART_THE_GAME , GAME_WON , GAME_LOST , GAME_NOT_OVER , GAME_ALREADY_STARTED } ;

    STARBASE_DOCKED_STATUS = { YES , NO }


CONCRETE_CONSTANTS
    normalMovementPowerUsage ,
    warpDrivePowerUsage ,
    asteroidCollisionPowerLost


PROPERTIES
    normalMovementPowerUsage : NAT &
    normalMovementPowerUsage = 5 &
    warpDrivePowerUsage : NAT  &
    warpDrivePowerUsage = 20 &
    asteroidCollisionPowerLost : NAT  &
    asteroidCollisionPowerLost = 10


DEFINITIONS
    isSpaceshipWithinTheGameRegion ( x , y ) == ( x : NAT1 & y : NAT1 & ( x |-> y : gameRegion ) ) ;
    isSpaceshipHitAsteroid ( x , y ) == ( x : NAT1 & y : NAT1 & ( x |-> y : asteroids ) ) ;
    isSpaceshipPowerSufficent ( currentPower , expectedMinPower ) == ( currentPower : NAT & expectedMinPower : NAT & ( currentPower >= expectedMinPower ) ) ;
    isSpaceshipDocked == ( xSpaceshipPosition |-> ySpaceshipPosition = starBase ) ;
    willSpaceshipDocked ( x , y ) == ( x |-> y = starBase ) ;
    isGameOver == isSpaceshipDocked or ( spaceshipCurrentPower < normalMovementPowerUsage ) ;



    ANIMATION_FUNCTION == ( { rr , cc , ii | rr : regionY & cc : regionX &
           ( IF ( cc = prj1 ( regionX , regionY ) ( starBase ) & rr = prj2 ( regionX , regionY ) ( starBase ) )
                THEN
                   IF ( cc = xSpaceshipPosition & rr = ( 8 - ySpaceshipPosition ) )
                       THEN
                            // Spaceship Docked
                            ii = 4
                       ELSE
                             // Star base
                            ii = 3
                       END
                ELSE
                   IF ( cc |-> ( 8 - rr ) : asteroids )
                   THEN
                       // Asteroid
                        ii = 1
                    ELSE
                       IF ( cc = xSpaceshipPosition & rr = ( 8 - ySpaceshipPosition ) )
                       THEN
                            // Spaceship
                            ii = 2
                       ELSE
                            // Empty Regions
                            ii = 0
                       END
                    END
                END ) } ) ;
     ANIMATION_IMG0 == "Gif_Images/Empty.gif" ;
     ANIMATION_IMG1 == "Gif_Images/Asteroid.gif" ;
     ANIMATION_IMG2 == "Gif_Images/Spaceship.gif" ;
     ANIMATION_IMG3 == "Gif_Images/Starbase.gif" ;
     ANIMATION_IMG4 == "Gif_Images/SpaceshipDockedAtStarbase.gif" ;



ABSTRACT_VARIABLES
    xSpaceshipPosition ,
    ySpaceshipPosition ,
    spaceshipCurrentPower ,
    noOfAsteroidCollitions ,
    spaceshipCurrentRegion ,
    spaceshipTakenRoute ,
    gameStatus


INVARIANT
    xSpaceshipPosition : regionX &
    ySpaceshipPosition : regionY &
    xSpaceshipPosition : NAT1 &
    ySpaceshipPosition : NAT1 &
    spaceshipCurrentPower : NAT &
    noOfAsteroidCollitions : NAT &
    spaceshipCurrentRegion : gameRegion &
    spaceshipTakenRoute : seq ( gameRegion ) &
    gameStatus <: GAME_STATUS


INITIALISATION
    xSpaceshipPosition := 1  ||
    ySpaceshipPosition := 1  ||
    spaceshipCurrentPower := 0 ||
    noOfAsteroidCollitions := 0 ||
    spaceshipCurrentRegion :=  homeBase ||
    spaceshipTakenRoute := [ homeBase  ] ||
    gameStatus := { GAME_NOT_STARTED }


OPERATIONS

    /* *******************************************************************************
        ** - OperationName -> newGame
        ** - Parameter -> Power of the spaceship
        ** - Assumption -> Consider the new game operation as a starting and resetting operation 
        ** - Result -> Starting the game or Resetting the spaceship to the initial state 
     ******************************************************************************* */

    status <-- newGame ( power ) =
        PRE
            // The spaceship need at least 25 power level to win (normal movement and Wrap Drive Movement)  
            status : GAME_STATUS & power : NAT & power > 25
        THEN
            IF
               ( GAME_NOT_STARTED : gameStatus & spaceshipCurrentRegion = homeBase )
            THEN
                //Starting the game
                spaceshipCurrentPower := power ||
                gameStatus := { GAME_NOT_OVER } ||
                status := START_THE_GAME
            ELSE
                //Restarting the game               
                xSpaceshipPosition := 1  ||
                ySpaceshipPosition := 1  ||
                spaceshipCurrentPower := power ||
                noOfAsteroidCollitions := 0 ||
                spaceshipCurrentRegion :=  homeBase ||
                spaceshipTakenRoute := [ homeBase  ] ||
                gameStatus := { GAME_NOT_OVER } ||
                status := RESTART_THE_GAME    //Display RESTART_THE_GAME
            END
        END ;



    /* *******************************************************************************
        ** - OperationName -> moveUp 
        ** - Parameter -> No params
        ** - Result -> Normal movement of the spaceship in upward direction to a 
                       square / region / cell
     ******************************************************************************* */

    status <-- moveUp =
        PRE
            status : NORMAL_MOVEMENT_REPORT
        THEN
            IF
                /* Checks if the game is start or game is already over */
                ( GAME_NOT_OVER : gameStatus )
            THEN
                IF
                    /*Checks whether Spaceship have sufficient amount of power to initiates the movement*/
                    ( isSpaceshipPowerSufficent ( spaceshipCurrentPower , normalMovementPowerUsage ) )
                THEN
                    IF
                     /*Checks whether the next region is out of boundary from Game region*/
                    ( isSpaceshipWithinTheGameRegion ( xSpaceshipPosition , succ ( ySpaceshipPosition ) ) )
                    THEN
                         IF
                        /*Checks whether the next region is has a Asteroid*/
                        not ( isSpaceshipHitAsteroid ( xSpaceshipPosition , succ ( ySpaceshipPosition ) ) )
                        THEN
                          IF
                          /*Checks whether game is won*/
                           ( willSpaceshipDocked ( xSpaceshipPosition , succ ( ySpaceshipPosition ) ) )
                          THEN
                              gameStatus := { GAME_WON }
                          END ||
                          spaceshipCurrentPower := spaceshipCurrentPower - normalMovementPowerUsage  ||
                          ySpaceshipPosition := succ ( ySpaceshipPosition ) ||
                          spaceshipCurrentRegion := ( xSpaceshipPosition |-> succ ( ySpaceshipPosition ) ) ||
                          spaceshipTakenRoute := spaceshipTakenRoute ^ [ xSpaceshipPosition |-> succ ( ySpaceshipPosition ) ] ||
                          status := SUCCESSFUL_MOVEMENT
                        ELSE
                          IF
                          /*Preventing spaceshipCurrentPower getting a minus value */
                           ( ( spaceshipCurrentPower - asteroidCollisionPowerLost ) > 0 )
                          THEN
                              spaceshipCurrentPower := spaceshipCurrentPower - asteroidCollisionPowerLost
                          ELSE
                              spaceshipCurrentPower := 0
                          END ||
                          noOfAsteroidCollitions := succ ( noOfAsteroidCollitions ) ||
                          status := MOVEMENT_FAILED_HIT_ASTEROID
                        END
                    ELSE
                      status := MOVEMENT_FAILED_REGION_OUT_OF_BOUND
                    END
                ELSE
                  IF
                    /* Checks if the game is over*/
                    ( isGameOver )
                  THEN
                      gameStatus := { GAME_LOST }
                  END ||
                  status := MOVEMENT_FAILED_INSUFFICIENT_POWER
                END
            ELSE
              IF
                /* Checks if the game is start*/
                ( GAME_NOT_STARTED : gameStatus )
              THEN
                  status := MOVEMENT_IMPOSSIBLE_PLEASE_START_THE_GAME
              ELSE
                  status := GAME_OVER_START_NEW_GAME
              END
            END
        END ;


     /* *******************************************************************************
        ** - OperationName -> moveDown 
        ** - Parameter -> No params
        ** - Result -> Normal movement of the spaceship in downward direction to a 
                       square / region / cell
     ******************************************************************************* */

    status <-- moveDown =
            PRE
                status : NORMAL_MOVEMENT_REPORT
            THEN
                IF
                    /* Checks if the game is start or game is already over */
                    ( GAME_NOT_OVER : gameStatus )
                THEN
                    IF
                        /*Checks whether Spaceship have sufficient amount of power to initiates the movement*/
                        ( isSpaceshipPowerSufficent ( spaceshipCurrentPower , normalMovementPowerUsage ) )
                    THEN
                        IF
                         /*Checks whether the next region is out of boundary from Game region*/
                        ( isSpaceshipWithinTheGameRegion ( xSpaceshipPosition , pred ( ySpaceshipPosition ) ) )
                        THEN
                             IF
                            /*Checks whether the next region is has a Asteroid*/
                            not ( isSpaceshipHitAsteroid ( xSpaceshipPosition , pred ( ySpaceshipPosition ) ) )
                            THEN
                              IF
                              /*Checks whether game is won*/
                               ( willSpaceshipDocked ( xSpaceshipPosition , pred ( ySpaceshipPosition ) ) )
                              THEN
                                  gameStatus := { GAME_WON }
                              END ||
                              spaceshipCurrentPower := spaceshipCurrentPower - normalMovementPowerUsage  ||
                              ySpaceshipPosition := pred ( ySpaceshipPosition ) ||
                              spaceshipCurrentRegion := ( xSpaceshipPosition |-> pred ( ySpaceshipPosition ) ) ||
                              spaceshipTakenRoute := spaceshipTakenRoute ^ [ xSpaceshipPosition |-> pred ( ySpaceshipPosition ) ] ||
                              status := SUCCESSFUL_MOVEMENT
                            ELSE
                                IF
                              /*Preventing spaceshipCurrentPower getting a minus value */
                               ( ( spaceshipCurrentPower - asteroidCollisionPowerLost ) > 0 )
                                  THEN
                                      spaceshipCurrentPower := spaceshipCurrentPower - asteroidCollisionPowerLost
                                  ELSE
                                      spaceshipCurrentPower := 0
                                  END ||
                                  noOfAsteroidCollitions := succ ( noOfAsteroidCollitions ) ||
                                  status := MOVEMENT_FAILED_HIT_ASTEROID
                                END
                        ELSE
                          status := MOVEMENT_FAILED_REGION_OUT_OF_BOUND
                        END
                    ELSE
                      IF
                        /* Checks if the game is over*/
                       ( isGameOver )
                      THEN
                          gameStatus := { GAME_LOST }
                      END ||
                      status := MOVEMENT_FAILED_INSUFFICIENT_POWER
                    END
                ELSE
                  IF
                    /* Checks if the game is start*/
                    ( GAME_NOT_STARTED : gameStatus )
                  THEN
                      status := MOVEMENT_IMPOSSIBLE_PLEASE_START_THE_GAME
                  ELSE
                      status := GAME_OVER_START_NEW_GAME
                  END
                END
            END ;

     /* *******************************************************************************
        ** - OperationName -> moveForward 
        ** - Parameter -> No params
        ** - Result -> Normal movement of the spaceship in Forward  direction to 
                       a square / space region / cell
     ******************************************************************************* */

    status <-- moveForward =
        PRE
            status : NORMAL_MOVEMENT_REPORT
        THEN
            IF
                /* Checks if the game is start or game is already over */
                ( GAME_NOT_OVER : gameStatus )
            THEN
                IF
                    /*Checks whether Spaceship have sufficient amount of power to initiates the movement*/
                    ( isSpaceshipPowerSufficent ( spaceshipCurrentPower , normalMovementPowerUsage ) )
                THEN
                    IF
                     /*Checks whether the next region is out of boundary from Game region*/
                    ( isSpaceshipWithinTheGameRegion ( succ ( xSpaceshipPosition ) , ySpaceshipPosition ) )
                    THEN
                         IF
                        /*Checks whether the next region is has a Asteroid*/
                        not ( isSpaceshipHitAsteroid ( succ ( xSpaceshipPosition ) , ySpaceshipPosition ) )
                        THEN
                          IF
                          /*Checks whether game is won*/
                           ( willSpaceshipDocked ( succ ( xSpaceshipPosition ) , ySpaceshipPosition ) )
                          THEN
                              gameStatus := { GAME_WON }
                          END ||
                          spaceshipCurrentPower := spaceshipCurrentPower - normalMovementPowerUsage  ||
                          xSpaceshipPosition := succ ( xSpaceshipPosition ) ||
                          spaceshipCurrentRegion := ( succ ( xSpaceshipPosition ) |-> ySpaceshipPosition ) ||
                          spaceshipTakenRoute := spaceshipTakenRoute ^ [ succ ( xSpaceshipPosition ) |-> ySpaceshipPosition ] ||
                          status := SUCCESSFUL_MOVEMENT
                        ELSE
                         IF
                          /*Preventing spaceshipCurrentPower getting a minus value */
                           ( ( spaceshipCurrentPower - asteroidCollisionPowerLost ) > 0 )
                          THEN
                              spaceshipCurrentPower := spaceshipCurrentPower - asteroidCollisionPowerLost
                          ELSE
                              spaceshipCurrentPower := 0
                          END ||
                          noOfAsteroidCollitions := succ ( noOfAsteroidCollitions ) ||
                          status := MOVEMENT_FAILED_HIT_ASTEROID
                        END
                    ELSE
                      status := MOVEMENT_FAILED_REGION_OUT_OF_BOUND
                    END
                ELSE
                  IF
                    /* Checks if the game is over*/
                   ( isGameOver )
                  THEN
                      gameStatus := { GAME_LOST }
                  END ||
                  status := MOVEMENT_FAILED_INSUFFICIENT_POWER
                END
            ELSE
              IF
                /* Checks if the game is start*/
                ( GAME_NOT_STARTED : gameStatus )
              THEN
                  status := MOVEMENT_IMPOSSIBLE_PLEASE_START_THE_GAME
              ELSE
                  status := GAME_OVER_START_NEW_GAME
              END
            END
        END ;



     /* *******************************************************************************
        ** - OperationName -> moveBackward 
        ** - Parameter -> No params
        ** - Result -> Normal movement of the spaceship in Backward  direction to a 
                       square / region / cell
     ******************************************************************************* */

    status <-- moveBackward =
        PRE
            status : NORMAL_MOVEMENT_REPORT
        THEN
            IF
                /* Checks if the game is start or game is already over */
                ( GAME_NOT_OVER : gameStatus )
            THEN
                IF
                    /*Checks whether Spaceship have sufficient amount of power to initiates the movement*/
                    ( isSpaceshipPowerSufficent ( spaceshipCurrentPower , normalMovementPowerUsage ) )
                THEN
                    IF
                     /*Checks whether the next region is out of boundary from Game region*/
                    ( isSpaceshipWithinTheGameRegion ( pred ( xSpaceshipPosition ) , ySpaceshipPosition ) )
                    THEN
                         IF
                        /*Checks whether the next region is has a Asteroid*/
                        not ( isSpaceshipHitAsteroid ( pred ( xSpaceshipPosition ) , ySpaceshipPosition ) )
                        THEN
                          IF
                           /*Checks whether game is won*/
                          ( willSpaceshipDocked ( pred ( xSpaceshipPosition ) , ySpaceshipPosition ) )
                          THEN
                              gameStatus := { GAME_WON }
                          END ||
                          spaceshipCurrentPower := spaceshipCurrentPower - normalMovementPowerUsage  ||
                          xSpaceshipPosition := pred ( xSpaceshipPosition ) ||
                          spaceshipCurrentRegion := ( pred ( xSpaceshipPosition ) |-> ySpaceshipPosition ) ||
                          spaceshipTakenRoute := spaceshipTakenRoute ^ [ pred ( xSpaceshipPosition ) |-> ySpaceshipPosition ] ||
                          status := SUCCESSFUL_MOVEMENT
                        ELSE
                         IF
                          /*Preventing spaceshipCurrentPower getting a minus value */
                           ( ( spaceshipCurrentPower - asteroidCollisionPowerLost ) > 0 )
                          THEN
                              spaceshipCurrentPower := spaceshipCurrentPower - asteroidCollisionPowerLost
                          ELSE
                              spaceshipCurrentPower := 0
                          END ||
                          noOfAsteroidCollitions := succ ( noOfAsteroidCollitions ) ||
                          status := MOVEMENT_FAILED_HIT_ASTEROID
                        END
                    ELSE
                      status := MOVEMENT_FAILED_REGION_OUT_OF_BOUND
                    END
                ELSE
                  IF
                    /* Checks if the game is over*/
                   ( isGameOver )
                  THEN
                      gameStatus := { GAME_LOST }
                  END ||
                  status := MOVEMENT_FAILED_INSUFFICIENT_POWER
                END
            ELSE
              IF
                /* Checks if the game is start*/
                ( GAME_NOT_STARTED : gameStatus )
              THEN
                  status := MOVEMENT_IMPOSSIBLE_PLEASE_START_THE_GAME
              ELSE
                  status := GAME_OVER_START_NEW_GAME
              END
            END
        END ;



     /* *******************************************************************************
        ** - OperationName -> engageWarpDrive
        ** - Parameter -> x coordinate and y coordinate of the expected location to move 
                          the spaceship
        ** - Result -> Warp Drive movement perform by spaceship to a given position 
                       in the space
     ******************************************************************************* */

    status <-- engageWarpDrive ( newRegionX , newRegionY ) =
        PRE
            status : WARP_DRIVE_REPORT & newRegionX : NAT1 & newRegionY : NAT1
        THEN
            IF
                /* Checks if the game is start or game is already over */
                ( GAME_NOT_OVER : gameStatus )
            THEN
                IF
                    /*Checks whether Spaceship have sufficient amount of power to initiates the movement*/
                    ( isSpaceshipPowerSufficent ( spaceshipCurrentPower , warpDrivePowerUsage ) )
                THEN
                    IF
                     /*Checks whether the next region is out of boundary from Game region*/
                    ( isSpaceshipWithinTheGameRegion ( newRegionX , newRegionY ) )
                    THEN
                         IF
                        /*Checks whether the next region is has a Asteroid*/
                        not ( isSpaceshipHitAsteroid ( newRegionX , newRegionY ) )
                        THEN
                           IF
                            /*Checks whether the next region is same region*/
                            not ( spaceshipCurrentRegion = newRegionX |-> newRegionY )
                            THEN
                                IF
                                /*Checks whether the starting region is Homebase and next region is Starbase*/
                                not ( spaceshipCurrentRegion = homeBase & willSpaceshipDocked ( newRegionX , newRegionY ) )
                                THEN
                                   IF
                                   /*Checks whether game is won*/
                                  ( willSpaceshipDocked ( newRegionX , newRegionY ) )
                                  THEN
                                      gameStatus := { GAME_WON }
                                  END ||
                                  spaceshipCurrentPower := spaceshipCurrentPower - warpDrivePowerUsage  ||
                                  xSpaceshipPosition := newRegionX ||
                                  ySpaceshipPosition := newRegionY ||
                                  spaceshipCurrentRegion := ( newRegionX |-> newRegionY ) ||
                                  spaceshipTakenRoute := spaceshipTakenRoute ^ [ newRegionX |-> newRegionY ] ||
                                  status := SUCCESSFUL_WARP_DRIVE
                                ELSE
                                  status := CANNOT_WARP_INTO_STARBASE_FROM_HOMEBASE
                                END
                            ELSE
                              status := CANNOT_WARP_INTO_SAME_REGION
                            END
                        ELSE
                          status := CANNOT_WARP_DRIVE_INTO_ASTEROID
                        END
                    ELSE
                      status := WARP_DRIVE_FAILED_REGION_OUT_OF_BOUND
                    END
                ELSE
                  IF
                    /* Checks if the game is over*/
                   ( isGameOver )
                  THEN
                      gameStatus := { GAME_LOST }
                  END ||
                  status := WARP_DRIVE_FAILED_INSUFFICIENT_POWER
                END
            ELSE
              IF
                /* Checks if the game is start*/
                ( GAME_NOT_STARTED : gameStatus )
              THEN
                  status := WARP_DRIVE_IMPOSSIBLE_PLEASE_START_THE_GAME
              ELSE
                  status := WARP_DRIVE_GAME_OVER_START_NEW_GAME
              END
            END
        END ;



     /* *******************************************************************************
        ** - OperationName -> missionStatus
        ** - Parameter -> No params
        ** - Result -> Provide the status of the spaceship such no of asteriods collisons happened,
                       current Power, current location
     ******************************************************************************* */

    currentLocationOfSpaceship , currentPowerOfSpaceship , totalNumberOfAsteroidCollitions <-- missionStatus =
        BEGIN
            currentLocationOfSpaceship := xSpaceshipPosition |-> ySpaceshipPosition ||
            currentPowerOfSpaceship := spaceshipCurrentPower ||
            totalNumberOfAsteroidCollitions := noOfAsteroidCollitions
        END ;



     /* *******************************************************************************
        ** - OperationName -> regionsVisited
        ** - Parameter -> No params
        ** - Result -> Provide the route of the Spaceship throughout the space regions
     ******************************************************************************* */

    missionRoute <-- regionsVisited =
        BEGIN
            missionRoute := spaceshipTakenRoute
        END ;



     /* *******************************************************************************
        ** - OperationName -> dockedAtStarbase
        ** - Parameter -> No params
        ** - Result -> Check if the Spaceship is docked in the starbase or not
     ******************************************************************************* */

    spaceshipDockedStatus <-- DockedAtStarbase =
        PRE
            spaceshipDockedStatus : STARBASE_DOCKED_STATUS
        THEN
            IF
                ( isSpaceshipDocked )
            THEN
                spaceshipDockedStatus := YES
            ELSE
                spaceshipDockedStatus := NO
            END
        END ;



     /* *******************************************************************************
        ** - OperationName -> gameStatus
        ** - Parameter -> No params
        ** - Result -> Track and Provide the status of the game for every specfic 
                       position of spaceship in the space regions
     ******************************************************************************* */

    status <-- statusOfGame =
        PRE
            status : GAME_STATUS
        THEN
            IF
                ( isSpaceshipDocked )
            THEN
                status := GAME_WON ||
                gameStatus := { GAME_WON }
            ELSE
                IF
                    ( isSpaceshipPowerSufficent ( spaceshipCurrentPower , normalMovementPowerUsage ) )
                THEN
                    status := GAME_NOT_OVER ||
                    gameStatus := { GAME_NOT_OVER }
                ELSE
                    IF
                    ( GAME_NOT_STARTED : gameStatus & spaceshipCurrentRegion = homeBase )
                    THEN
                        status := GAME_NOT_STARTED ||
                        gameStatus := { GAME_NOT_STARTED }
                    ELSE
                        status := GAME_LOST ||
                        gameStatus := { GAME_LOST }
                    END
                END
            END
        END
END
