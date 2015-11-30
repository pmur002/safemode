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
%- maybe also 'usage' for other objects documented here.
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
a documment describing the use of \dQuote{safe mode}).
}
\value{
%%  ~Describe the value returned
%%  If it is a LIST, use
%%  \item{comp1 }{Description of 'comp1'}
%%  \item{comp2 }{Description of 'comp2'}
%% ...
}
\references{
%% ~put references to the literature/web site here ~
}
\author{
Paul Murrell
}
\note{
%%  ~~further notes~~
}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\seealso{
%% ~~objects to See Also as \code{\link{help}}, ~~~
}
\examples{
safemode(infile=system.file("scripts", "example.R", package="safemode"))
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
\keyword{ debugging }
