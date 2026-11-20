import Development.AutomorphicArithmetic.Foundations.Convolution.Cbcc

/- English proof (translation)
The claim follows from `UpperTheory.ConvolutionTheory.GM.gm_of_bcfl PositivityTheory.Rg.Tf.Loc.bcflUnit`.
-/
theorem UpperTheory.ConvolutionTheory.Sph.gm : UpperTheory.ConvolutionTheory.GM.GM := UpperTheory.ConvolutionTheory.GM.gm_of_bcfl PositivityTheory.Rg.Tf.Loc.bcflUnit

/- English proof (translation)
The claim follows from `UpperTheory.ConvolutionTheory.T.liftAll (UpperTheory.ConvolutionTheory.T.liftStep (UpperTheory.ConvolutionTheory.T.coreLift UpperTheory.ConvolutionTheory.ci UpperTheory.ConvolutionTheory.Sph.gm))`.
-/
theorem UpperTheory.ConvolutionTheory.Sph.liftAll : UpperTheory.ConvolutionTheory.T.LiftAll :=
  UpperTheory.ConvolutionTheory.T.liftAll (UpperTheory.ConvolutionTheory.T.liftStep (UpperTheory.ConvolutionTheory.T.coreLift UpperTheory.ConvolutionTheory.ci UpperTheory.ConvolutionTheory.Sph.gm))
