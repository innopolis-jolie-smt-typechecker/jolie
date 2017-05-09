include "console.iol"

main 
{
 a = 2;
 b = 3;
 if ( a ) {
  println@Console( a + b )()
 }else{
  println@Console( "Hello, world!" )()
 }
}