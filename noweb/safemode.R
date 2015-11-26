###  Original code and documentation copyright Ross Ihaka, 2011
### 
###  Modifications copyright Paul Murrell, 2015
###
###  Distributed under the terms of GPL3, but may also be
###  redistributed under any later version of the GPL.
###
###  Safe mode for R
###
###  Synopsis:
###
###  This function provides an environment that provides some 
###  protection from stupidity arising from laziness
###
###    safemode()
###    ...
###    q()
###
###  Exit from safe mode using using q()
###
###  This is best regarded as an exercise in getting familar
###  with R's condition system and a demonstration of how
###  to write an interpreted REPL and an exploration of 
###  the 'codetools' and 'CodeDepends' packages.

timeDB <- new.env()
depDB <- new.env()
safemode <- local({
    warningCalls <- vector("list", 50)
    warningMessages <- character(50)
    nwarnings <- 0
    renewwarnings <- TRUE
    newwarnings <- FALSE
    age <- function(x) {
        get(x, timeDB, inherits=FALSE)
    }
    deps <- function(x) {
        get(x, depDB, inherits=FALSE)
    }    
    stale <- function(x) {
        dependents <- deps(x)
        length(dependents) &&
            (any(age(x) < sapply(dependents, age)) || 
             any(sapply(dependents, stale)))
    }
    staleWarnMsg <- function(deps) {
        N <- length(deps)
        if (N == 1) {
            paste0("Symbol '", deps, "' is stale!")
        } else if (N == 2) {
            paste0("Symbols '",
                   paste(deps, collapse="' and '"),
                   "' are stale!")
        } else {
            paste0("Symbols '",
                   paste(paste(deps[-N], collapse="', '"),
                         deps[N], sep="', and '"),
                   "' are stale!")
        }
    }
    incompleteParse <- function(e) {
        (inherits(e, "error") &&
         grepl("unexpected end of input", e$message))
    }
    handleParseError <- function(e) {
        msg = strsplit(conditionMessage(e), "\n")[[1]]
        errortxt = msg[1]
        msg = gsub("[0-9]+: ", "", msg[-c(1, length(msg))])
        msg = msg[length(msg) - 1:0]
        if (length(msg) == 1)
            msg = paste(" in: \"", msg, "\"\n", sep = "")
        else
            msg = paste(" in:\n\"",
                        paste(msg, collapse = "\n"),
                        "\"\n", sep = "")
        cat("Error",
            gsub("\n.*", "",
                 gsub("<text>:[0-9]+:[0-9]+", "",
                      errortxt)),
            msg, sep = "")
    }
    handleError <- function(e) {
        cat("Error in", deparse(conditionCall(e)),
            ":", conditionMessage(e), "\n")
    }
    handleValue <- function(e) {
        if (e$visible) {
            print(e$value)
        }
    }
    warningHandler <- function(w) {
        newwarnings <<- TRUE
        if (renewwarnings) {
            renewwarnings <<- FALSE
            nwarnings <<- 0
        }
        n <- nwarnings + 1
        if (n <= 50) {
            warningCalls[[n]] <<- conditionCall(w)
            warningMessages[n] <<- conditionMessage(w)
            nwarnings <<- n
        }
        invokeRestart("muffleWarning")
    }        
    tryCatchWithWarnings <- function(expr) {
        withCallingHandlers(tryCatch(expr,
                                     error = function(e) e),
                            warning = warningHandler)
    }
    displayWarnings <- function(n) {
        if (n <= 10) {
            print(warnings())
        } else if (n < 50) {
            cat("There were",
                nwarnings,
                "warnings (use warnings() to see them)\n")
        } else {
            cat("There were 50 or more warnings",
                "(use warnings() to see the first 50)\n")
        }
    }
    isQuitCall <- function(e) {
        (!inherits(e, "error") &&
          length(e) == 1 &&
          deparse(e[[1]], nlines = 1) == "q()")
    }
    repl <- function(env, debug, infile) {
        prompt <- "safe> "
        cmd <- character()
        if (is.null(infile)) {
            batch <- FALSE
        } else {
            batch <- TRUE
            con <- file(infile, "r")
        }
        repeat {
            ans <- tryCatch(
	        repeat {
	            repeat {
		        if (batch) {
		            cmd <- c(cmd, readLines(con, n=1))
		        } else {
		            cmd <- c(cmd, readline(prompt))
		        }
		        if (grepl("^#", cmd)) {
		            if (batch) {
		                cat(paste0("safe> ", cmd), "\n")
		            }
		            cmd <- character()
		            break
		        }
		        ans <- tryCatch(parse(text = cmd), error = function(e) e)
		        if (inherits(ans, "error")) {
			    if (incompleteParse((ans))) {
			        prompt <- "safe+ "
			    } else {
			        handleParseError(ans)
			        prompt <- "safe> "
			        cmd <- character()
			    }
			} else {
			    special <- TRUE
			    if (length(ans) == 0) {
			        if (batch) {
			            cat("\n")
			        }
			        cmd <- character()
			        break
			    } else if (isQuitCall(ans)) {
			        return()
			    } else if (grepl("^safemode\\(",
			                   deparse(ans[[1]], nlines = 1))) {
			        cat("Error: You can't call safemode() while in \"safe mode\"\n")
			        break
			    } else {
			        special <- FALSE
			    }
			    if (!special) {
			        renewwarnings <<- TRUE
			        newwarnings <<- FALSE
			        for(e in ans) {
			            dummy <- function() {}
				    body(dummy) <- e
				    vars <- findGlobals(dummy)
				    tracked <- vars[vars %in% ls(timeDB)]
				    if (debug) {
				        cat(paste("globals: ", paste(vars, collapse=", "), "\n"))
				        cat(paste("tracked: ", paste(tracked, collapse=", "), "\n"))
				    }
				    if (length(tracked) > 0) {
				        staleDeps <- sapply(tracked, stale)
				        if (any(staleDeps)) {
				            withCallingHandlers(warning(staleWarnMsg(tracked[staleDeps])),
				                                warning = warningHandler)
				        }
				    }
				    code <- deparse(e)                                 
				    e <- tryCatchWithWarnings(withVisible(eval(e,
				                                               envir = env)))
				    if (inherits(e, "error")) {
				        handleError(e)
				    } else {
				        if (batch) {
				            cat(paste0(c("safe> ",
					                 rep("safe+ ",
					                     max(0, length(code) - 1))),
					               code), sep="\n")
				        }
				        handleValue(e)
				        # test for whether expression was an assignment
					sc <- readScript("", txt=code)
					info <- scriptInfo(sc)
					inputs <- info[[1]]@inputs
					outputs <- info[[1]]@outputs
					updates <- info[[1]]@updates
					if (debug) {
					    cat(paste("inputs: ", paste(inputs, collapse=", "), "\n"))
					    cat(paste("outputs: ", paste(outputs, collapse=", "), "\n"))
					    cat(paste("updates: ", paste(updates, collapse=", "), "\n"))
					}
					assignment <- FALSE
					symbol <- character()
					if (length(outputs) > 0) {
					    symbol <- c(symbol, outputs)
					    assignment <- TRUE
					}
					if (length(updates) > 0) {
					    symbol <- c(symbol, updates)
					    assignment <- TRUE    
					}
					if (assignment) {
					    for (i in symbol) {
					        assign(i, as.numeric(Sys.time()), envir=timeDB)
					        assign(symbol, tracked, envir=depDB)
					    }
					    if (debug) {
					        cat("Time stamp database:\n")
					        print(sapply(ls(timeDB), get, envir=timeDB))
					        cat("Dependencies database:\n")
					        print(sapply(ls(depDB), get, envir=depDB))
					    }
					}
				    }
			        }
			        if (newwarnings) {
			            warnings = warningCalls
			            names(warnings) = warningMessages
			            assign("last.warning",
			                   warnings[1:nwarnings],
			                   "package:base")
			            displayWarnings(nwarnings)
			        }
			    }
			    prompt <- "safe> "
			    cmd <- character()
			}
		    }
	        }, interrupt = function(x) x)
	    if (inherits(ans, "interrupt")) {
	        cat("\nInterrupt!\n")
	        prompt <- "script> "
	        cmd <- character()
	    } else {
	        stop("Interrupt catcher caught non-interrupt")
	    }
        }
        if (batch) {
            close(con)
        }
    }

    function(debug=FALSE, infile=NULL) {
        repl(sys.parent(), debug, infile)
        invisible()
    }
})
