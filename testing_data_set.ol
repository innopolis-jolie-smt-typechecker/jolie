include "console.iol"

main 
{
 in = 1;
 db = 1.0;
 n = in instanceof number; 
 n = db instanceof number
 a = 2;
 b = 3;
 if ( a ) {
  println@Console( a + b )()
 }else{
  println@Console( "Hello, world!" )()
 }
 a[ 0 ] = 0;
 a[ 1 ] = 5;
 a[ 2 ] = "Hello";
 a[ 3 ] = 2.5
 str = "hello world";
 
 getTemperature@Forecast( city )( temperature ) |
	getData@Traffic( city )( traffic );

	println@Console( "Request served!" )() 
 ms = "a" / 5;
  
 ss = 5 * "a";
  
 answer = false;
  
 question = "13";
  
 question = 12;
  
 question = answer;
  
 qwe = answer;
  
 println@Console( answer )();
  
 if (answer) {
    println@Console( "Hello, world!" + string(answer) )()
  };
  
 if (9 < 6) {
    println@Console( "collpase" )()
  };
  qwe = !false;
  
 while (qwe) {
  	qwe = false
  };
  
 for (i = 10, i > 0, i--) {
  	println@Console( i )()
  }
}
}