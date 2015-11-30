\name{safemode}
\alias{safemode}
\title{
  Start a \dQuote{safe mode} session.
}
\description{
  Starts a sub-session on the command line.  The prompt changes to
  \preformatted{safe>} and warnings are issued when a \dQuote{stale} symbol is 
  used in an expression.  A symbol is stale if it is older than any of
  the symbols that it depends upon. 
}
\usage{
safemode(debug = FALSE, infile = NULL)
}
\arguments{
  \item{debug}{
    A logical indicating whether to output (rather messy) debugging information.
  }
  \item{infile}{
    If not \code{NULL}, should be the name of a file containing R code. 
  }
}
\details{
  The intended use of \dQuote{safe mode} is to interactively monitor
  and warn the user when they do something stupid like submit expressions
  from an R script file in the wrong order.
  
  Type \code{q()} to exit \dQuote{safe mode} (and return to the normal
  R prompt).
  
  If the \code{infile} argument is specified, \code{safemode()} runs
  in batch mode;  this is useful for generating a log of a 
  \sQuote{safe mode} session (for example, if you want to write 
  a document describing the use of \dQuote{safe mode}).
}
\value{
  This function is only useful for its side-effect of running
  a \dQuote{safe mode} sub-session.
}
\references{
  The package source is available from github,
  \url{https://github.com/pmur002/safemode}.

  The source is based on the \code{script()} function by Ross Ihaka,
  \url{https://www.stat.auckland.ac.nz/~ihaka/software/R-script/R-script.html}.
}
\author{
  Paul Murrell
}
\note{
  The sub-session command line does not work exactly like the
  normal R command line.  For example, there is no auto-completion.
}
\examples{
safemode(infile=system.file("scripts", "example.R", package="safemode"))
}
\keyword{ debugging }
