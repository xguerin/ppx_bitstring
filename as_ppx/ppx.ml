let () =
  ignore(Ppx_bitstring.extension);
  Ppx_driver.run_as_ppx_rewriter ()
;;
