import NQueens.{e, tauler}
import scala.io.StdIn.readLine

object CrowdedChessboard extends App {
  println("CROWDED CHESSBOARD")
  print("Entra la mida del tauler: ")
  val n: Int = readLine().toInt
  println("Opcions \n\t '1' per encoding quadratic \n\t '2' per encoding logaritmic")
  print("Tria la opcio d'encoding: ")
  val opcio: Int = readLine().toInt
  print("Vols trencar simetries (S/N)? ")
  val trencaSim: String = readLine()
  print("Vols afegir clausules implicades (S/N)? ")
  val afegirImplicades: String = readLine()
  print("Vols afegir un cavall mes (UNSAT) (S/N)? ")
  val unsat: String = readLine()

  println(n);


  val e = new ScalAT("Crowded")


  val taulerReines: Array[Array[Int]] = e.newVar2DArray(n, n)
  val taulerTorres = e.newVar2DArray(n, n)
  val taulerAlfils = e.newVar2DArray(n, n)
  val taulerCavalls = e.newVar2DArray(n, n)

  // Que la torre i la reina no estigui en més d'una fila o columna
  unaFilaUnaColumna()
  // Que no es matin les reines per la diagonal
  diagonal()
  // Trenquem simetries dels àlfils
  if(trencaSim == "S")
    simetries()
  // Que els alfils no es matin
  colorcarAlfils()
  // Que no es matin els cavalls
  colorCavalls()
  // Posar implicites
  if(afegirImplicades == "S")
    implicades()
  // Que no estiguin 2 al mateix lloc
  for(i <- 0 until n; j <- 0 until n) e.addAMOLog(List(taulerReines(i)(j), taulerTorres(i)(j), taulerAlfils(i)(j), taulerCavalls(i)(j)))


  def unaFilaUnaColumna() = {
    for(i <- taulerReines) {
      if(opcio == 1) e.addEOQuad(i.toList) else e.addEOLog(i.toList)
    }
    for(i <- taulerReines.transpose) {
      if(opcio == 1) e.addEOQuad(i.toList) else e.addEOLog(i.toList)
    }

    for(i <- taulerTorres) {
      if(opcio == 1) e.addEOQuad(i.toList) else e.addEOLog(i.toList)
    }
    for(i <- taulerTorres.transpose) {
      if(opcio == 1) e.addEOQuad(i.toList) else e.addEOLog(i.toList)
    }
  }

  def diagonal() = {
    for(i <- 0 to 2*n-2) {
      if(opcio == 1) e.addAMOQuad((for(j <- 0 until n; k <- 0 until n; if j+k == i) yield taulerReines(j)(k)).toList)
      else e.addAMOLog((for(j <- 0 until n; k <- 0 until n; if j+k == i) yield taulerReines(j)(k)).toList)
    }
    for(i <- -n+1 until n) {
      if(opcio == 1) e.addAMOQuad((for(j <- 0 until n; k <- 0 until n; if j-k == i) yield taulerReines(j)(k)).toList)
      else e.addAMOLog((for(j <- 0 until n; k <- 0 until n; if j-k == i) yield taulerReines(j)(k)).toList)
    }
  }

  def simetries() = {
    e.addClause(taulerAlfils(0)(0) :: List())
    e.addClause(taulerAlfils(n-1)(0) :: List())

    e.addClause(-taulerAlfils(0)(n-1) :: List())
    e.addClause(-taulerAlfils(n-1)(n-1) :: List())

    e.addClause(-taulerReines(0)(0) :: List())
    e.addClause(-taulerTorres(0)(0) :: List())
    e.addClause(-taulerCavalls(0)(0) :: List())
    e.addClause(-taulerReines(n-1)(0) :: List())
    e.addClause(-taulerTorres(n-1)(0) :: List())
    e.addClause(-taulerCavalls(n-1)(0) :: List())
  }

  def colorcarAlfils() = {
    for(i <- 1 until 2*n-2) {
      if (opcio == 1) e.addEOQuad((for(j <- 0 until n; k <- 0 until n; if j+k == i) yield taulerAlfils(j)(k)).toList)
      else e.addEOLog((for(j <- 0 until n; k <- 0 until n; if j+k == i) yield taulerAlfils(j)(k)).toList)
    }
    for(i <- -n+2 until n-1) {
      if(opcio == 1) e.addEOQuad((for(j <- 0 until n; k <- 0 until n; if j-k == i) yield taulerAlfils(j)(k)).toList)
      else e.addEOLog((for(j <- 0 until n; k <- 0 until n; if j-k == i) yield taulerAlfils(j)(k)).toList)
    }
  }

  def colorCavalls() = {
    val cavallsMax = Map(5 -> 5, 6 -> 9, 7 -> 11, 8 -> 21, 9 -> 29, 10 -> 37, 11 -> 47, 12 -> 57, 13 -> 69, 14 -> 81, 15 -> 94, 16 -> 106)
    e.addEK(taulerCavalls.flatMap(_.toList).toList, cavallsMax.getOrElse(n, 0))

    for(i <- 0 until n-1; j <- 0 until n) {
      val moviments = List((i+1, j-2), (i+2, j-1), (i+2, j+1), (i+1, j+2))
      for((f, c) <- moviments; if f < n && c >= 0 && c < n) {
        if(opcio == 1) e.addAMOQuad(List(taulerCavalls(i)(j), taulerCavalls(f)(c)))
        else e.addAMOLog(List(taulerCavalls(i)(j), taulerCavalls(f)(c)))
      }
    }
  }

  def implicades() = {
    e.addEK(taulerReines.flatMap(_.toList).toList, n)
    e.addEK(taulerTorres.flatMap(_.toList).toList, n)
    e.addEK(taulerAlfils.flatMap(_.toList).toList, 2*n-2)
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
