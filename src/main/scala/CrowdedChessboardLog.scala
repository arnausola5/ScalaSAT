import NQueens.{e, tauler}

import scala.io.StdIn.readLine

object CrowdedChessboardLog extends App {

  val e = new ScalAT("Crowded")

  print("Entra la mida del tauler: ")
  val n: Int = readLine().toInt
  print("Vols trencar simetries (S/N)? ")
  val trencaSim: String = readLine()
  print("Vols afegir clausules implicades (S/N)? ")
  val afegirImplicades: String = readLine()

  println()

  val taulerReines: Array[Array[Int]] = e.newVar2DArray(n, n)

  for(i <- taulerReines) e.addEOLog(i.toList)
  for(i <- taulerReines.transpose) e.addEOLog(i.toList)
  for(i <- 0 to 2*n-2)
    e.addAMOLog((for(j <- 0 until n; k <- 0 until n; if j+k == i) yield taulerReines(j)(k)).toList)
  for(i <- -n+1 until n)
    e.addAMOLog((for(j <- 0 until n; k <- 0 until n; if j-k == i) yield taulerReines(j)(k)).toList)

  val taulerTorres = e.newVar2DArray(n, n)

  for(i <- taulerTorres) e.addEOLog(i.toList)
  for(i <- taulerTorres.transpose) e.addEOLog(i.toList)

  val taulerAlfils = e.newVar2DArray(n, n)



  for(i <- 1 until 2*n-2)
    e.addEOLog((for(j <- 0 until n; k <- 0 until n; if j+k == i) yield taulerAlfils(j)(k)).toList)
  for(i <- -n+2 until n-1)
    e.addEOLog((for(j <- 0 until n; k <- 0 until n; if j-k == i) yield taulerAlfils(j)(k)).toList)

  val taulerCavalls = e.newVar2DArray(n, n)

  for(i <- 0 until n-1; j <- 0 until n) {
    val moviments = List((i+1, j-2), (i+2, j-1), (i+2, j+1), (i+1, j+2))
    for((f, c) <- moviments; if f < n && c >= 0 && c < n) e.addAMOLog(List(taulerCavalls(i)(j), taulerCavalls(f)(c)))
  }

  val cavallsMax = Map(5 -> 5, 6 -> 9, 7 -> 11, 8 -> 21, 9 -> 29, 10 -> 37, 11 -> 47, 12 -> 57, 13 -> 69, 14 -> 81, 15 -> 94, 16 -> 106)

  e.addEK(taulerCavalls.flatMap(_.toList).toList, cavallsMax.getOrElse(n, 0))

  if(afegirImplicades == "S") {
    e.addEK(taulerReines.flatMap(_.toList).toList, n)
    e.addEK(taulerTorres.flatMap(_.toList).toList, n)
    e.addEK(taulerAlfils.flatMap(_.toList).toList, n * 2 - 2)
  }

  for(i <- 0 until n; j <- 0 until n) e.addAMOLog(List(taulerReines(i)(j), taulerTorres(i)(j), taulerAlfils(i)(j), taulerCavalls(i)(j)))

  if(trencaSim == "S") {
    e.addClause(taulerAlfils(0)(0) :: List())
    e.addClause(taulerAlfils(n - 1)(0) :: List())

    e.addClause(-taulerAlfils(0)(n - 1) :: List())
    e.addClause(-taulerAlfils(n - 1)(n - 1) :: List())

    e.addClause(-taulerReines(0)(0) :: List())
    e.addClause(-taulerTorres(0)(0) :: List())
    e.addClause(-taulerCavalls(0)(0) :: List())
    e.addClause(-taulerReines(n - 1)(0) :: List())
    e.addClause(-taulerTorres(n - 1)(0) :: List())
    e.addClause(-taulerCavalls(n - 1)(0) :: List())
  }

  val result = e.solve()

  def getPositions(tauler: Array[Array[Int]]) = tauler
    .map(_.map((i: Int) => if (e.getValue(i)) "X " else "· "))
    .map(_.mkString(""))
    .mkString("\n")

  def mostraSolucio(taulerReines: Array[Array[Int]], taulerTorres: Array[Array[Int]], taulerAlfils: Array[Array[Int]], taulerCavalls: Array[Array[Int]]) =
    for(i <- 0 until taulerReines.size; j <- 0 until taulerReines.size) {
      if(e.getValue(taulerCavalls(i)(j))) print("C ")
      else if(e.getValue(taulerTorres(i)(j))) print("T ")
      else if(e.getValue(taulerAlfils(i)(j))) print("A ")
      else if(e.getValue(taulerReines(i)(j))) print("R ")
      else print("· ")

      if(j == taulerReines.size - 1) println();
    }

  println(result)
  if(result.satisfiable) println(mostraSolucio(taulerReines, taulerTorres, taulerAlfils, taulerCavalls))
}

// n = 14, logarítmic => 160.3371276
// n = 15, logarítmic => 2061.8895603