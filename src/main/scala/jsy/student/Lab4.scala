package jsy.student

import jsy.lab4.Lab4Like

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * Michael Gohde
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */
  //The following were checked in the scala interpreter and appear to produce correct output.
  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => Nil
    case h1 :: (t1 @ (h2 :: rest)) => if(h1==h2) h1::compressRec(rest) else h1::compressRec(t1)
  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => if(acc.isEmpty) h::Nil else if(h==acc.head) acc else h::acc
  }

  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => Nil
    case h :: t => f(h) match {
      case Some(s) => s::t
      case None => h::mapFirst(t)(f)
    }
  }
  
  /* Trees */

  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty => acc
      case Node(l, d, r) => loop(f(loop(acc, l), d), r) //loop(loop(f(acc, d), l), r) //TODO: Consider restructuring this.
    }
    loop(z, t)
  }

  // An example use of foldLeft
  def sum(t: Tree): Int = foldLeft(t)(0){ (acc, d) => acc + d }

  // Create a tree from a list. An example use of the
  // List.foldLeft method.
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }

  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = foldLeft(t)((true, None: Option[Int])){
      case ((b: Boolean, acc: Option[Int]), v) => acc match { //First tuple is our real accumulator.
        case Some(rv) => if(rv<v) (b, Some(v)) else (false, Some(v))
        case None => (b, Some(v))
      }
    }
    b
  }

  /* Type Inference */

  // While this helper function is completely given, this function is
  // worth studying to see how library methods are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }

  def pairToMap(l: List[(String, Typ)]): Map[String, Typ] = l match{
    case head :: rest => head match {
      case (s, t) => Map(s -> t) ++ pairToMap(rest)
    }

    case Nil => Map()
  }
  
  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => env.get(x) match {
        case Some(vtype) => vtype
        case None => err(TUndefined, e)
      }
      case Decl(mode, x, e1, e2) => typeof(env, e2) //It appears that TypeDecl wants the type of the second expression given that ... uhhhh...
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typeof(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) =>
        ???
      case Binary(Minus|Times|Div, e1, e2) => {
        val t1=typeof(env, e1)
        val t2=typeof(env, e2)

        (t1, t2) match {
          case (TNumber, TNumber) => TNumber
          case (_, _) => err(TNumber, e)
        }
      }
      case Binary(Eq|Ne, e1, e2) => {
        //Y'know what? I could probably just use (typeof(), typeof()) match {}
        val t1=typeof(env, e1)
        val t2=typeof(env, e2)

        if(t1==t2) TBool else err(t1, e)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => {
        val t1=typeof(env, e1)
        val t2=typeof(env, e2)

        (t1, t2) match {
          case (TNumber, TNumber) => TBool
          case (_, _) => err(TBool, e)
        }
      }
      case Binary(And|Or, e1, e2) =>{
        val t1=typeof(env, e1)
        val t2=typeof(env, e2)

        (t1, t2) match {
          case (TBool, TBool) => TBool
          case (_, _) => err(TBool, e)
        }
      }
      case Binary(Seq, e1, e2) => typeof(env, e2)
      case If(e1, e2, e3) => {
        val t1=typeof(env, e1)
        val t2=typeof(env, e2)
        val t3=typeof(env, e3)

        t1 match{
          case TBool => (t2, t3) match {
            case (TBool, TBool) => TBool
            case (TNumber, TNumber) => TNumber
            case (TString, TString) => TString
            case (TUndefined, TUndefined) => TUndefined
            case (_, _) => err(TUndefined, e)
          }
          case _ => err(t1, e)
        }
      }
      case Function(p, params, tann, e1) => {
        // Mtyp allows us to distinguish between const and name declarations (ie. consts and pointers?)
        // Bind to env1 an environment that extends env with an appropriate binding if <- THIS IS IMPORTANT! If the function calls itself, we need to add its name to the type environment.
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          /***** Add cases here *****/
            case(None, None) => env //Neither name nor type; env should just be passed through.
            case(None, Some(ftype)) => env //Has a type but no name
            case(Some(fname), Some(ftype)) => env ++ Map(fname -> ftype)//Has a name and type. Do we now need to add a binding for this function?

            case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = env1++params //TODO: Extract types from the MTyp list and properly extend env2!
        // Infer the type of the function body
        val t1 = typeof(env1, e1)

        // Check with the possibly annotated return type
        tann match {
          case Some(ftype) => if(ftype==t1) t1 else err(t1, e1)
          case None => t1
        }
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params zip args).foreach { // Each element in params is matched and extended with an element in args.
            zipped => zipped match {
              case ((pname, pmtyp), pmexpr) => if(pmtyp.t!=typeof(env, pmexpr)) err(typeof(env, pmexpr), e)
              case _ => err(TUndefined, e)
            }
          };
          tret
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields.map(arg => arg match {
        case (s, expr) => (s, typeof(env, expr))
        case _ => err(TUndefined, e)
      }))
      case GetField(e1, f) => e1 match {
        case Obj(fields) => fields.get(f) match {
          case Some(x) => typeof(env, x)
          case None => err(TUndefined, e)
        }
        case _ => err(TUndefined, e)
      }
    }
  }
  
  
  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case _ => ??? // delete this line when done
    }
  }

  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = ???
    loop(e0, 0)
  }

  def findInParams(x: String, params: List[(String, MTyp)]): Option[MTyp] = {
    params.foreach(v => v match {
      case (s, m) => if(s==x) m
    })

    None
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, esub, x))
        /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, substitute(e1, esub, x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1, esub, x), substitute(e2, esub, x))
      case If(e1, e2, e3) => If(substitute(e1, esub, x), substitute(e2, esub, x), substitute(e3, esub, x))
      case Var(y) => if(y.equals(x)) esub else e
      case Decl(mode, y, e1, e2) => if(y==x) Decl(mode, y, substitute(e1, esub, x), e2) else Decl(mode, y, substitute(e1, esub, x), substitute(e2, esub, x))
        /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) => p match{
        case None => findInParams(x, params) match {
          case Some(m) => e
          case None => Function(p, params, tann, substitute(e1, esub, x))
        }
        case Some(fn) => if(x!=fn) e else Function(p, params, tann, substitute(e1, esub, x))
        //case _ => ???
      }

      case Call(e1, args) => Call(substitute(e1, esub, x), args.map(av => substitute(av, esub, x))) // We should also sub on args...

        /***** New cases for Lab 4 */
      case Obj(fields) => Obj(fields.map(args => args match {
        case (fname, fexpr) => (fname, substitute(fexpr, esub, x))
      }))
      case GetField(e1, f) => GetField(substitute(e1, esub, x), f)/*e1 match {
        case Obj(fields) => fields.get(f) match {
          case Some(expr) =>
        }
        case _ => GetField(substitute(e1, esub, x), f)
      }*/
    }

    val fvs = freeVars(???)
    def fresh(x: String): String = if (???) fresh(x + "$") else x
    subst(???)
  }

  /* Rename bound variables in e */
  def rename(e: Expr)(fresh: String => String): Expr = {
    def ren(env: Map[String,String], e: Expr): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        case Print(e1) => Print(ren(env, e1))

        case Unary(uop, e1) => Unary(uop, ren(env, e1))
        case Binary(bop, e1, e2) => Binary(bop, ren(env, e1), ren(env, e2))
        case If(e1, e2, e3) => If(ren(env, e1), ren(env, e2), ren(env, e3))

        case Var(y) => Var(fresh(y))
        case Decl(mode, y, e1, e2) => {
          val yp = fresh(y)
          Decl(mode, yp, ren(env, e1), ren(env, e2))
        }

        case Function(p, params, retty, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None => ???
            case Some(x) => ???
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            ???
          }
          ???
        }

        case Call(e1, args) => ???

        case Obj(fields) => ???
        case GetField(e1, f) => ???
      }
    }
    ren(empty, e)
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst => isValue(e)
    case MName => if(isValue(e)) true else isRedex(mode, e)
  }

  def strGt(a: String, b: String): Boolean = {
    var i=0;

    for(i <- 0 to math.min(a.size, b.size)) {
      if(a.charAt(i)>b.charAt(i)) true else if(a.charAt(i)<b.charAt(i)) false
    }

    false
  }

  def allAreVals(fields: Map[String, Expr]): Boolean = {
    fields.foreach(fv => fv match {
      case (fn, fe) => if(!isValue(fe)) false
    })

    true
  }

  def firstFields(fields: Map[String, Expr]): Obj = {
      val vlist=fields.toList;
      val newMap=mapFirst(vlist)(v => v match {
        case (str, expr) => if(isValue(expr)) None else Some((str, step(expr)))
        case _ => None
      })

      Obj(newMap.toMap)
    }

  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
        /***** Cases needing adapting from Lab 3. */
      case Unary(Neg, v1) if isValue(v1) => v1 match {
        case N(n) => N(-n)
      }

      case Unary(Not, v1) if isValue(v1) => v1 match {
        case B(b) => B(!b)
      }

      case Binary(bop, v1, v2) if(isValue(v1)&&isValue(v2)) => {
        (v1, v2) match {
          case (N(a), N(b)) => bop match {
            case Plus => N(a+b)
            case Minus => N(a-b)
            case Times => N(a*b)
            case Div => N(a/b)

            case Gt => B(a>b)
            case Ge => B(a>=b)
            case Lt => B(a<b)
            case Le => B(a<=b)
            case Eq => B(a==b)
            case Ne => B(a!=b)

            case _ => throw StuckError(e)
          }

          case (S(a), S(b)) => bop match {
            case Plus => S(a+b)
            case Eq => B(a==b)
              //3 cheers for only having to implement one comparison function.
            case Gt => B(strGt(a, b))
            case Lt => B(!strGt(a, b) && a!=b)
            case Ge => B(strGt(a, b) || a==b)
            case Le => B(!strGt(a, b))
            case Ne => B(a!=b)

            case _ => throw StuckError(e)
          }

          case(B(a), B(b)) => bop match {
              //These should be applicable to booleans as well.
            case Eq => B(a==b)
            case Ne => B(a==b)

            case And => if(a) B(b) else B(false)
            case Or => if(a) B(true) else B(b)

            case _ => throw StuckError(e)
          }

          case _ => throw StuckError(e)
        }
      }

      case Binary(bop, v1, e2) if(isValue(v1)) => bop match {
        case Seq => e2

          //Let's just handle the second half of SearchBinary here:
        case _ => Binary(bop, v1, step(e2))
      }

      case If(v1, v2, v3) if(isValue(v1)) => v1 match {
        case B(a) => if(a) v2 else v3
        case _ => throw StuckError(e)
      }

        /***** More cases here */
      case Call(v1, args) if isValue(v1) => //Fundamental idea: all elements in the call get replaced with the contents of args.
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args
            if (params.length==args.length) {
              val e1p = pazip.foldRight(e1) {
                //We're going from last to first
                case (((s: String, mt: MTyp), e: Expr), b: Expr) => substitute(b, e, s)
              }
              p match {
                case None => e1p
                case Some(x1) => substitute(e1p, v1, x1) //Put the function into itself if it's recursive.
              }
            }
            else {
              //Assumption: These are all our call by value function parameters?
              val pazipp = mapFirst(pazip) {
                ???
              }
              ???
            }
          }
          case _ => throw StuckError(e)
        }
        /***** New cases for Lab 4. */
      case GetField(v1, f) if isValue(v1) => v1 match {
        case Obj(fields) => fields.get(f) match {
          case Some(fexp) => fexp
          case _ => throw StuckError(e)
        }
      }

      case Decl(mode, x, v1, e2) if(isValue(v1)) => substitute(e2, v1, x)

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
        /***** Cases from Lab 3. */
      case Unary(uop, e1) => Unary(uop, step(e1))
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)
        /***** More cases here */
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      case Decl(mode, x, e1, e2) => Decl(mode, x, step(e1), e2)
        /***** Cases needing adapting from Lab 3 */
      case Call(v1 @ Function(_, _, _, _), args) => ???
      case Call(e1, args) => ???

        /***** New cases for Lab 4. */
      case Obj(fields) if(!allAreVals(fields)) => firstFields(fields)
      case GetField(e1, f) => GetField(step(e1), f)
      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }
  
  
  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}

