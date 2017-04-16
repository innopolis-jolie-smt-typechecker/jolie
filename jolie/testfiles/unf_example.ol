


define Arithmetic{a = 3.4 + 2.1;b = true;  c = 10L;      a = 5;      b = 3 + 2;      c = 4 - 3;      d = 7 / c;      e = 5 * d;      f = --a + 2;     g = f % 5}
define Casting{    s = "10";    n = 5 + int( s ); // n = 15
    d = "1.3";    n = double( d );    n = int( n )}

define TypeCheck{    s = "10";    n = s instanceof string;    n = s instanceof int;    n = (s = 10) instanceof int}

define Strings{    s = "This is " + "a string\n"}

define Defined
{
    a = 1;
    n = is_defined( a );
    undef( a )
}


define Arrays
{
    a[ 0 ] = 0;
    a[ 1 ] = "Hello";
    a[ 2 ] = 2.5;
    n = #a
}

define Parallel
{
    c = 3 | b = 4;
    { a[0] = 3; a[1] = 6 }
    |    { b[0] = 6; b[1] = 2 }
}

define InputChoice{    [ buy( stock )( response ) {    	buy@Exchange( stock )( response )    } ] { println@Console( "Buy order forwarded" )() }    [ sell( stock )( response ) {    	sell@Exchange( stock )( response )    }] { println@Console( "Sell order forwarded" )() }}
define Conditions
{    if ( a == 5 && a < 6) {
        a = 1
    } else if ( a > 5 ) {        a = 2
    } else if ( a < 5 ) {
        a = 3
    } else if ( a != 5 ) {        a = 4
    } else if ( a >= 5 ) {
        a = 5
    } else if ( a <= 5 ) {
        a = 6    }
}

define Loops{
    a = 0;
    while ( a < 10 ) {
        a++
    };    for ( i = 0, i < 50 || i != 50, i++ ) {
  	a[i] += i    }
}

define DataStructures
{
    animals.pet[0].name = "cat";
    animals.pet[1].name = "dog";
    animals.wild[0].name = "tiger";
    animals.wild[1].name = "lion";
      foreach ( kind : animals ){
    	  for ( i = 0, i < #animals.( kind ), i++  ){
    		  println@Console( "animals." + kind + "[" + i + "].name = " +
    			  animals.( kind )[ i ].name )()
    	  }
      };
    with ( animals ){
    	.pet[ 0 ].name = "cat";
    	.pet[ 1 ].name = "dog";
    	.wild[ 0 ].name = "tiger";
    	.wild[ 1 ].name = "lion"
    };
    zoo.sector_a << animals;
    undef( animals );
    with ( a.b.c ){
    	.d[ 0 ] = "zero";
    	.d[ 1 ] = "one";
    	.d[ 2 ] = "two";
    	.d[ 3 ] = "three"
    };
    currentElement[ 0 ] -> a.b.c.d[ i ];
    for ( i = 0, i < #a.b.c.d, i++ ){
    	println@Console( currentElement )()
    }
}
constants {
	Server_location = "socket://localhost:8080",
	ALARM_TIMEOUT = 2000,
	standard_gravity = 9.8
}

type SumRequest: void {	.number [ 2, * ]: int}interface SumInterface {	RequestResponse:		sum( SumRequest )( int )}inputPort SumInput {	Location: "socket://localhost:8000/"	Protocol: soap	Interfaces: SumInterface}outputPort SumServ {	Location: "socket://localhost:8000/"	Protocol: soap	Interfaces: SumInterface}


main
{    scope ( myScope )    {        install(            TypeMismatch => println@Console( myScope.TypeMismatch )()
        )        // code
    };    globalVariable = 3;    a = global.globalVariable;    println@Console( "Hello, world!" )()}