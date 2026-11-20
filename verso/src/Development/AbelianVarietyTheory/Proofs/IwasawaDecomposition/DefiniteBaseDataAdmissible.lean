import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldsIsConductorPrimesModulus

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem.DatLaws

open NumberField IsDedekindDomain in

/- English proof (translation)
Introduce `B X Ch hCh hH`. Prove the components needed by the constructor for the conclusion. Use `case fields => exact _root_.GlobalTheory.Mem.FieldsLaws.fields_ok B`. Use `case fieldsConditions => exact (_root_.GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1`. Use `case embeddingStarConj => exact _root_.GlobalTheory.Mem.Base.baseData_embedding_conj B X Ch`.

Use `case f_eq => exact (_root_.GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).2`. Use `case primes => exact (_root_.GlobalTheory.BasePrimes.primes_ok B X).1`. Use `case piG_cong => exact (_root_.GlobalTheory.BasePrimes.primes_ok B X).2`. Use `case cond => exact _root_.GlobalTheory.Mem.Base.fields_isCond B X`. Use `case chars => exact hCh`.

Use `case hecke => exact hH`. Use `case wts => exact _root_.GlobalTheory.Mem.Base.wts_isOk B`. Use `case e_even => exact _root_.GlobalTheory.Mem.Base.dat_e_even B X Ch`. Use `case sizes => exact _root_.GlobalTheory.Mem.Base.primes_sizes B X`.
-/
theorem _root_.GlobalTheory.Mem.DatLaws.dat_ok : ∀ (B : _root_.GlobalTheory.Mem.Base)
    (X : _root_.GlobalTheory.Mem.PreX B.toPre)
    (Ch : _root_.Formalism.L2.Col.Chars B.fields (B.primes X) B.R.m),
    Ch.Ok → Ch.FromHecke B.wts B.embLL →
      (B.dat X Ch).Ok := by
  intro B X Ch hCh hH
  constructor
  case fields => exact _root_.GlobalTheory.Mem.FieldsLaws.fields_ok B
  case fieldsConditions => exact (_root_.GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1
  case embeddingStarConj => exact _root_.GlobalTheory.Mem.Base.baseData_embedding_conj B X Ch
  case f_eq => exact (_root_.GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).2
  case primes => exact (_root_.GlobalTheory.BasePrimes.primes_ok B X).1
  case piG_cong => exact (_root_.GlobalTheory.BasePrimes.primes_ok B X).2
  case cond => exact _root_.GlobalTheory.Mem.Base.fields_isCond B X
  case chars => exact hCh
  case hecke => exact hH
  case wts => exact _root_.GlobalTheory.Mem.Base.wts_isOk B
  case e_even => exact _root_.GlobalTheory.Mem.Base.dat_e_even B X Ch
  case sizes => exact _root_.GlobalTheory.Mem.Base.primes_sizes B X

end GlobalTheory.Mem.DatLaws
