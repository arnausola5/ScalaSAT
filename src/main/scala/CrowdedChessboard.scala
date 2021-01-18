import NQueens.{e, tauler}
import scala.io.StdIn.readLine

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

  val e = new ScalAT("Crowded")

  // Mida del tauler
  println("CROWDED CHESSBOARD")
  print("Entra la mida del tauler: ")
  val n: Int = readLine().toInt
  println("Opcions \n\t '1' per encoding quadratic \n\t '2' per encoding logaritmic")
  print("Tria la opcio d'encoding: ")
  val opcio: Int = readLine().toInt
  print("Vols trencar simetries (S/N)? ")
  val trencaSim: String = readLine()
  print("Vols afegir clausules implicades (S/N)? ")
  val implicades: String = readLine()
  print("Vols afegir un cavall mes (UNSAT) (S/N)? ")
  val unsat: String = readLine()


  // A cada fila i a cada columna nomes hi pot anar 1 element del tauler donat mitjançant ExactlyOne
  // Per la opcio 1 s'usa l'encoding quadratic del EO i per la 2 l'encoding Logaritmic
  def files_i_columnes(tauler:Array[Array[Int]], opcio:Int) = {
    for (i <- tauler)
      if (opcio == 1) e.addEOQuad(i.toList) else e.addEOLog(i.toList)
    for (i <- tauler.transpose)
      if(opcio == 1) e.addEOQuad(i.toList) else e.addEOLog(i.toList)
  }


  def clausulesReines(tauler:Array[Array[Int]], opcio:Int) = {

    files_i_columnes(tauler, opcio)

    for (i <- 0 to 2 * n - 2)
      if (opcio == 1) e.addAMOQuad((for (j <- 0 until n; k <- 0 until n; if j + k == i) yield tauler(j)(k)).toList)
      else e.addAMOLog((for (j <- 0 until n; k <- 0 until n; if j + k == i) yield tauler(j)(k)).toList)

    for (i <- -n + 1 until n)
      if (opcio == 1) e.addAMOQuad((for (j <- 0 until n; k <- 0 until n; if j - k == i) yield tauler(j)(k)).toList)
      else e.addAMOLog((for (j <- 0 until n; k <- 0 until n; if j - k == i) yield tauler(j)(k)).toList)
  }

  def clausulesTorres(tauler:Array[Array[Int]], opcio:Int ) = {
    files_i_columnes(tauler,opcio)
  }

  def clausulesAlfils(tauler:Array[Array[Int]], opcio:Int) = {

    for (i <- 0 to 2 * n - 2)
      if (opcio == 1) e.addAMOQuad((for (j <- 0 until n; k <- 0 until n; if j + k == i) yield tauler(j)(k)).toList)
      else e.addEOLog((for (j <- 0 until n; k <- 0 until n; if j + k == i) yield tauler(j)(k)).toList)

    for (i <- -n + 1 until n)
      if (opcio == 1) e.addAMOQuad((for (j <- 0 until n; k <- 0 until n; if j - k == i) yield tauler(j)(k)).toList)
      else e.addEOLog((for (j <- 0 until n; k <- 0 until n; if j - k == i) yield tauler(j)(k)).toList)

  }

  def clausulesCavalls(tauler:Array[Array[Int]],opcio:Int) = {

    val cavallsMax = Map(5 -> 5, 6 -> 9, 7 -> 11, 8 -> 21, 9 -> 29, 10 -> 37, 11 -> 47, 12 -> 57, 13 -> 69, 14 -> 81, 15 -> 94, 16 -> 106)
    var nCavalls = cavallsMax.getOrElse(n, 0)
    if (unsat == 'S')
      nCavalls = nCavalls +1

    e.addEK(taulerCavalls.flatMap(_.toList).toList, nCavalls)

    for(i <- 0 until n-1; j <- 0 until n) {
      val moviments = List((i+1, j-2), (i+2, j-1), (i+2, j+1), (i+1, j+2))
      for((f, c) <- moviments; if f < n && c >= 0 && c < n)
        if (opcio == 1) e.addAMOQuad(List(tauler(i)(j), tauler(f)(c)))
        else e.addAMOLog(List(tauler(i)(j), tauler(f)(c)))
    }
  }

  def simetriesAlfils() = {
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


  def AMOCaselles(opcio:Int) = {


    for(i <- 0 until n; j <- 0 until n)
      if (opcio == 1) e.addAMOQuad(List(taulerReines(i)(j), taulerTorres(i)(j), taulerAlfils(i)(j), taulerCavalls(i)(j)))
      else e.addAMOLog(List(taulerReines(i)(j), taulerTorres(i)(j), taulerAlfils(i)(j), taulerCavalls(i)(j)))
  }

  def clauslesImplicades() = {

    e.addEK(taulerReines.flatMap(_.toList).toList, n)
    e.addEK(taulerTorres.flatMap(_.toList).toList, n)
    e.addEK(taulerAlfils.flatMap(_.toList).toList, 2*n - 2)
  }

  val taulerReines: Array[Array[Int]] = e.newVar2DArray(n, n)
  clausulesReines(taulerReines,opcio)
  /*for(i <- taulerReines) e.addEOLog(i.toList)
  for(i <- taulerReines.transpose) e.addEOLog(i.toList)
  for(i <- 0 to 2*n-2)
    e.addAMOLog((for(j <- 0 until n; k <- 0 until n; if j+k == i) yield taulerReines(j)(k)).toList)
  for(i <- -n+1 until n)
    e.addAMOLog((for(j <- 0 until n; k <- 0 until n; if j-k == i) yield taulerReines(j)(k)).toList)
  */
  val taulerTorres = e.newVar2DArray(n, n)
  clausulesTorres(taulerTorres,opcio)
  /*
  for(i <- taulerTorres) e.addEOLog(i.toList)
  for(i <- taulerTorres.transpose) e.addEOLog(i.toList)
  */
  val taulerAlfils = e.newVar2DArray(n, n)
  clausulesAlfils(taulerAlfils,opcio)

  /*
  e.addClause(taulerAlfils(0)(0) :: List())
  e.addClause(taulerAlfils(n-1)(0) :: List())

  e.addClause(-taulerAlfils(0)(n-1) :: List())
  e.addClause(-taulerAlfils(n-1)(n-1) :: List())

  for(i <- 1 until 2*n-2)
    e.addEOLog((for(j <- 0 until n; k <- 0 until n; if j+k == i) yield taulerAlfils(j)(k)).toList)
  for(i <- -n+2 until n-1)
    e.addEOLog((for(j <- 0 until n; k <- 0 until n; if j-k == i) yield taulerAlfils(j)(k)).toList)
  */

  val taulerCavalls = e.newVar2DArray(n, n)
  clausulesCavalls(taulerCavalls,opcio)
  /*
  for(i <- 0 until n-1; j <- 0 until n) {
    val moviments = List((i+1, j-2), (i+2, j-1), (i+2, j+1), (i+1, j+2))
    for((f, c) <- moviments; if f < n && c >= 0 && c < n) e.addAMOLog(List(taulerCavalls(i)(j), taulerCavalls(f)(c)))
  }

  val cavallsMax = Map(5 -> 5, 6 -> 9, 7 -> 11, 8 -> 21, 9 -> 29, 10 -> 37, 11 -> 47, 12 -> 57, 13 -> 69, 14 -> 81, 15 -> 94, 16 -> 106)


  e.addEK(taulerCavalls.flatMap(_.toList).toList, cavallsMax.getOrElse(n, 0))
  e.addEK(taulerReines.flatMap(_.toList).toList, n)
  e.addEK(taulerTorres.flatMap(_.toList).toList, n)
  e.addEK(taulerAlfils.flatMap(_.toList).toList, 2*n - 2)
  */

  AMOCaselles(opcio)
  //for(i <- 0 until n; j <- 0 until n) e.addAMOLog(List(taulerReines(i)(j), taulerTorres(i)(j), taulerAlfils(i)(j), taulerCavalls(i)(j)))

  if (implicades == 'S')
    clauslesImplicades()

  if (trencaSim == 'S')
    simetriesAlfils()
  /*
  e.addClause(-taulerReines(0)(0) :: List())
  e.addClause(-taulerTorres(0)(0) :: List())
  e.addClause(-taulerCavalls(0)(0) :: List())
  e.addClause(-taulerReines(n-1)(0) :: List())
  e.addClause(-taulerTorres(n-1)(0) :: List())
  e.addClause(-taulerCavalls(n-1)(0) :: List())*/


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
  /* if(result.satisfiable) println(getPositions(taulerReines))
  println()
  if(result.satisfiable) println(getPositions(taulerTorres))
  println()
  if(result.satisfiable) println(getPositions(taulerAlfils))
  println()
  if(result.satisfiable) println(getPositions(taulerCavalls)) */

  if(result.satisfiable) println(mostraSolucio(taulerReines, taulerTorres, taulerAlfils, taulerCavalls))
}

// n = 14, logarítmic => 160.3371276
// n = 15, logarítmic => 2061.8895603