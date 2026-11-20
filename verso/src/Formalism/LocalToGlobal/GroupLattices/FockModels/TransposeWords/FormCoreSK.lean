import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.ProdBlockEmbMonomial
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingDividedAdjoint
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingRowAction
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingHighestWeightProof
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.CwlApplyWordAppendSingle
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.LowerTriangularOverField
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.WeylFormNondegenerateGlobal
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FormSK

namespace Formalism.L2.G.Model.TS.Top

open Formalism.L2.G.Model.TS Formalism.GradedWeylDivisibility

/- English proof (translation)
The claim follows from `Formalism.L2.G.Model.TS.fock_pairing_bilinear`.
-/
theorem fockRBilin : FockRBilin := Formalism.L2.G.Model.TS.fock_pairing_bilinear
/- English proof (translation)
The claim follows from `Formalism.L2.G.Model.TS.fock_pairing_map`.
-/
theorem fockRMap : FockRMap := Formalism.L2.G.Model.TS.fock_pairing_map
/- English proof (translation)
The claim follows from `Formalism.L2.G.Model.TS.fock_pairing_monomial`.
-/
theorem fockRMonomial : FockRMonomial := Formalism.L2.G.Model.TS.fock_pairing_monomial
/- English proof (translation)
The claim follows from `Formalism.L2.G.Model.TS.fock_pairing_block`.
-/
theorem fockRBlock : FockRBlock := Formalism.L2.G.Model.TS.fock_pairing_block
/- English proof (translation)
The claim follows from `Formalism.L2.G.Model.TS.highest_weight_norm`.
-/
theorem hWNorm : HWNorm := Formalism.L2.G.Model.TS.highest_weight_norm
/- English proof (translation)
The claim follows from `Formalism.L2.G.Model.TS.fock_pairing_divided_adjoint`.
-/
theorem fockRRowDivAdj : FockRRowDivAdj := Formalism.L2.G.Model.TS.fock_pairing_divided_adjoint
/- English proof (translation)
The claim follows from `Formalism.L2.G.Model.TS.fock_pairing_row_action`.
-/
theorem fockRRowAct : FockRRowAct := Formalism.L2.G.Model.TS.fock_pairing_row_action
/- English proof (translation)
The claim follows from `Formalism.L2.G.Model.TS.fock_pairing_highest_weight_proof`.
-/
theorem fock_pairing_highest_weight : FockPairingHighestWeight := Formalism.L2.G.Model.TS.fock_pairing_highest_weight_proof
/- English proof (translation)
The claim follows from `Formalism.L2.G.Model.TS.weyl_pairing`.
-/
theorem weylPair : WeylPair := Formalism.L2.G.Model.TS.weyl_pairing
/- English proof (translation)
The claim follows from `Formalism.L2.G.Model.TS.dual_weyl_inclusion`.
-/
theorem dualWeylIn : DualWeylIn := Formalism.L2.G.Model.TS.dual_weyl_inclusion
/- English proof (translation)
The claim follows from `Formalism.L2.G.Model.TS.nondegenerate_over_field`.
-/
theorem nondegK : NondegK := Formalism.L2.G.Model.TS.nondegenerate_over_field
/- English proof (translation)
The claim follows from `Formalism.L2.G.Model.TS.formCoreSK_of Formalism.L2.G.Model.TS.weyl_form_nondegenerate_global`.
-/
theorem formCoreSK : FormCoreSK := Formalism.L2.G.Model.TS.formCoreSK_of Formalism.L2.G.Model.TS.weyl_form_nondegenerate_global

end Formalism.L2.G.Model.TS.Top
