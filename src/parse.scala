import scala.util.parsing.combinator._
import java.io.FileReader

// EXTENDED FROM A BASE FILE WRITTEN BY RUZICA PISKAC,
// CPSC 454 PROFESSOR AT YALE UNIVERSITY

object VCGen {

    /* Arithmetic expressions. */
    trait ArithExp

    case class Num(value: Int) extends ArithExp
    case class Var(name: String) extends ArithExp
    case class Read(name: String, ind: ArithExp) extends ArithExp
    case class Add(left: ArithExp, right: ArithExp) extends ArithExp
    case class Sub(left: ArithExp, right: ArithExp) extends ArithExp
    case class Mul(left: ArithExp, right: ArithExp) extends ArithExp
    case class Div(left: ArithExp, right: ArithExp) extends ArithExp
    case class Mod(left: ArithExp, right: ArithExp) extends ArithExp
    case class Parens(a: ArithExp) extends ArithExp

    /* Comparisons of arithmetic expressions. */
    type Comparison = Product3[ArithExp, String, ArithExp]

    /* Boolean expressions. */
    trait BoolExp

    case class BCmp(cmp: Comparison) extends BoolExp
    case class BNot(b: BoolExp) extends BoolExp
    case class BDisj(left: BoolExp, right: BoolExp) extends BoolExp
    case class BConj(left: BoolExp, right: BoolExp) extends BoolExp
    case class BParens(b: BoolExp) extends BoolExp

    /* Statements and blocks. */
    trait Statement
    type Block = List[Statement]

    case class Assign(x: String, value: ArithExp) extends Statement
    case class Write(x: String, ind: ArithExp, value: ArithExp) extends Statement
    case class ParAssign(x1: String, x2: String, value1: ArithExp, value2: ArithExp) extends Statement
    case class If(cond: BoolExp, th: Block, el: Block) extends Statement
    case class While(cond: BoolExp, inv: List[Assertion], body: Block) extends Statement

    /* Assertions. */
    trait Assertion

    case class ACmp(cmp: Comparison) extends Assertion
    case class ANot(a: Assertion) extends Assertion
    case class AAnd(left: Assertion, right: Assertion) extends Assertion
    case class AOr(left: Assertion, right: Assertion) extends Assertion
    case class AImply(left: Assertion, right: Assertion) extends Assertion
    case class AParens(a: Assertion) extends Assertion
    case class QUniv(left: List[String], right: Assertion) extends Assertion
    case class QExist(left: List[String], right: Assertion) extends Assertion

    /* Complete programs. */
    type Program = Product4[String, List[Assertion], List[Assertion], Block]

    object ImpParser extends RegexParsers {
        /* General helpers. */
        def pvar  : Parser[String] = "\\p{Alpha}(\\p{Alnum}|_)*".r

        /* Parsing for ArithExp. */
        def num   : Parser[ArithExp] = "-?\\d+".r ^^ (s => Num(s.toInt))

        def atom  : Parser[ArithExp] =
            "(" ~> aexp <~ ")" |
            pvar ~ ("[" ~> aexp <~ "]") ^^ {case v ~ i => Read(v, i)} |
            num | pvar ^^ { Var(_) } |
            "-" ~> atom ^^ { Sub(Num(0), _) }

        def factor: Parser[ArithExp] =
            atom ~ rep("*" ~ atom | "/" ~ atom | "%" ~ atom) ^^ {
                case left ~ list => (left /: list) {
                    case (left, "*" ~ right) => Mul(left, right)
                    case (left, "/" ~ right) => Div(left, right)
                    case (left, "%" ~ right) => Mod(left, right)
                }
            }

        def term  : Parser[ArithExp] =
            factor ~ rep("+" ~ factor | "-" ~ factor) ^^ {
                case left ~ list => (left /: list) {
                    case (left, "+" ~ right) => Add(left, right)
                    case (left, "-" ~ right) => Sub(left, right)
                }
            }

        def aexp  : Parser[ArithExp] = term

        /* Parsing for Comparison. */
        def comp  : Parser[Comparison] =
            aexp ~ ("=" | "<=" | ">=" | "<" | ">" | "!=") ~ aexp ^^ {
                case left ~ op ~ right => (left, op, right)
            }

        /* Parsing for BoolExp. */
        def batom : Parser[BoolExp] =
            "(" ~> bexp <~ ")" | comp ^^ { BCmp(_) } | "!" ~> batom ^^ { BNot(_) }

        def bconj : Parser[BoolExp] =
            batom ~ rep("&&" ~> batom) ^^ {
                case left ~ list => (left /: list) { BConj(_, _) }
            }

        def bdisj : Parser[BoolExp] =
            bconj ~ rep("||" ~> bconj) ^^ {
                case left ~ list => (left /: list) { BDisj(_, _) }
            }

        def bexp  : Parser[BoolExp] = bdisj

        /* Parsing for Statement and Block. */
        def block : Parser[Block] = rep(stmt)

        def stmt  : Parser[Statement] =
            pvar ~ ("[" ~> aexp <~ "]") ~ (":=" ~> aexp <~ ";") ^^ {
                case v ~ i ~ e => Write(v, i, e)
            } |
            (pvar <~ ":=") ~ (aexp <~ ";") ^^ {
                case v ~ e => Assign(v, e)
            } |
            (pvar <~ ",") ~ (pvar <~ ":=") ~ (aexp <~ ",") ~ (aexp <~ ";") ^^ {
                case v1 ~ v2 ~ e1 ~ e2 => ParAssign(v1, v2, e1, e2)
            } |
            ("if" ~> bexp <~ "then") ~ (block <~ "else") ~ (block <~ "end") ^^ {
                case c ~ t ~ e => If(c, t, e)
            } |
            ("if" ~> bexp <~ "then") ~ (block <~ "end") ^^ {
                case c ~ t => If(c, t, Nil)
            } |
            ("while" ~> (bexp ~ rep("inv" ~> assn)) <~ "do") ~ (block <~ "end") ^^ {
                case c ~ i ~ b => While(c, i, b)
            }

        /* Parsing for Assertion. */
        def aatom : Parser[Assertion] =
            "(" ~> assn <~ ")" | ("forall" ~> rep(pvar) <~ ",") ~ assn ^^ { case q ~ a => QUniv(q, a) } | ("exists" ~> rep(pvar) <~ ",") ~ assn ^^ { case q ~ a => QExist(q, a) } | comp ^^ { ACmp(_) } | "!" ~> aatom ^^ { ANot(_) }

        def aconj : Parser[Assertion] =
            aatom ~ rep("&&" ~> aatom) ^^ {
                case left ~ list => (left /: list) { AAnd(_, _) }
            }

        def adisj : Parser[Assertion] =
            aconj ~ rep("||" ~> aconj) ^^ {
                case left ~ list => (left /: list) { AOr(_, _) }
            }

        def aimp : Parser[Assertion] =
            adisj ~ rep("==>" ~> adisj) ^^ {
                case left ~ list => (left /: list) { AImply(_, _) }
            }

        def assn  : Parser[Assertion] = aimp

        /* Parsing for Program. */
        def prog  : Parser[Program] =
            ("program" ~> pvar) ~ rep("pre" ~> assn) ~ rep("post" ~> assn) ~ ("is" ~> block <~ "end") ^^ {
                case n ~ pre ~ post ~ b => (n, pre, post, b)
            }
    }

    def main(args: Array[String]): Unit = {
        val reader = new FileReader(args(0))
        import ImpParser._;
        println(parseAll(prog, reader))
    }
}
