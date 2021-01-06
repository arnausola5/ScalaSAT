import NQueens.{e, tauler}

object CrowdedChessboard extends App {


/*  board
 size Q  R  B  KN
   5  5  5  8   5
                6 *
   6  6  6 10   9
               10 *
   7  7  7 12  11
               12 *
   8  8  8 14  21
               22 *
   9  9  9 16  29
               30 *
  10 10 10 18  37
               38 *
  11 11 11 20  47
               48 *
  12 12 12 22  57
               58 *
  13 13 13 24  69
               70 *
  14 14 14 26  81
               82 *
  15 15 15 28  94
               95 *
  16 16 16 30 109
              110 *
  */

  for(i<-0 until 8)
    println(i)



  val e = new ScalAT("Crowded")

  // Mida del tauler
  val n = 5

  val taulerReines: Array[Array[Int]] = e.newVar2DArray(n, n)

  for(i <- taulerReines) e.addEOQuad(i.toList)
  for(i <- taulerReines.transpose) e.addEOQuad(i.toList)
  for(i <- 0 to 2*n-2)
    e.addAMOQuad((for(j <- 0 until n; k <- 0 until n; if j+k == i) yield taulerReines(j)(k)).toList)
  for(i <- -n+1 until n)
    e.addAMOQuad((for(j <- 0 until n; k <- 0 until n; if j-k == i) yield taulerReines(j)(k)).toList)

  val taulerTorres = e.newVar2DArray(n, n)

  for(i <- taulerTorres) e.addEOQuad(i.toList)
  for(i <- taulerTorres.transpose) e.addEOQuad(i.toList)

  val taulerAlfils = e.newVar2DArray(n, n)

  e.addClause(taulerAlfils(0)(0) :: List())
  e.addClause(taulerAlfils(n-1)(0) :: List())
  e.addClause(-taulerAlfils(0)(n-1) :: List())
  e.addClause(-taulerAlfils(n-1)(n-1) :: List())

  for(i <- 1 until 2*n-2)
    e.addEOQuad((for(j <- 0 until n; k <- 0 until n; if j+k == i) yield taulerAlfils(j)(k)).toList)
  for(i <- -n+2 until n-1)
    e.addEOQuad((for(j <- 0 until n; k <- 0 until n; if j-k == i) yield taulerAlfils(j)(k)).toList)

  // val taulerCavalls = e.newVar2DArray(n, n)

  for(i <- 0 until n; j <- 0 until n) e.addAMOQuad(List(taulerReines(i)(j), taulerTorres(i)(j), taulerAlfils(i)(j)))

  val result = e.solve()

  def getPositions(tauler: Array[Array[Int]]) = tauler
    .map(_.map((i: Int) => if (e.getValue(i)) "X " else "· "))
    .map(_.mkString(""))
    .mkString("\n")

  println(result)
  if(result.satisfiable) println(getPositions(taulerReines))
  println()
  if(result.satisfiable) println(getPositions(taulerTorres))
  println()
  if(result.satisfiable) println(getPositions(taulerAlfils))


}
