let _ =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some Debug);
  Compiler_lib.Rules.program ()
