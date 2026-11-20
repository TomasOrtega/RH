import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsReadingStepMoveBasePointsOneOffLevelPrime
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBasePointUnitaryNormalisesLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeImagePointOfLift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotTopPtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesAwayLevelAndTypePrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.AdForm.TopMove

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC GlobalTheory.TwU

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre}

def offPl (I : TC B X) (u : B.Word) (a : I.ι) : Set (HeightOneSpectrum (𝓞 B.host.F)) :=
  {v | (∃ j, (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal) ∧ (B.T u : 𝓞 B.host.F) ∉ v.asIdeal ∧ ¬ I.UnderQ a v}

/- English proof (translation)
Use `(Set.finite_iUnion fun j : Fin 2 => GlobalTheory.TwU.MoveOff.finite_over (F := B.host.F) (B.host.g_prime j).ne_zero).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨⟨j, hj⟩, -, -⟩`. Conclude with `Set.mem_iUnion.2 ⟨j, hj⟩`.
-/
theorem offPl_finite (I : TC B X) (u : B.Word) (a : I.ι) : (offPl I u a).Finite := by
  refine (Set.finite_iUnion fun j : Fin 2 =>
    GlobalTheory.TwU.MoveOff.finite_over (F := B.host.F) (B.host.g_prime j).ne_zero).subset ?_
  rintro v ⟨⟨j, hj⟩, -, -⟩
  exact Set.mem_iUnion.2 ⟨j, hj⟩

/- English proof (translation)
The claim follows from `R.key onto := R.onto lb := R.lb k_std := hstd k_off := hoff k_T := hT pt := fun c => by have e : y c * k' (chOf c) * ((k' (chOf c))⁻¹ * k (chOf c)) = y c * k (chOf c) := by group rw [e] exact R.pt c lev := fun c x q hq => by have e : y c * k' (chOf c) * x * ((k' (chOf c))⁻¹ * k ( …`.
-/
theorem reads_move' (I : TC B X) {u : B.Word} {a : I.ι} {i : ℕ} {Ch : Type}
    {chOf : (I.stp u a i).Cl → Ch} {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (TC.GA B (B.R.N i))}
    {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u a i).Cl → TC.GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → TC.GA B (B.R.N i)} (R : I.Reads u a i chOf Lb U chi y st k) (k' : Ch → TC.GA B (B.R.N i))
    (U' : Ch → Subgroup (TC.GA B (B.R.N i))) (chi' : ∀ β, U' β →* ℂˣ)
    (hU : ∀ β x, x ∈ U' β ↔ k' β * x * (k' β)⁻¹ ∈ U β)
    (hchi : ∀ β (x : U' β), chi' β x = chi β ⟨k' β * x.1 * (k' β)⁻¹, (hU β x.1).1 x.2⟩)
    (hstd : ∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, TC.PtOf ((k' β)⁻¹ * k β) p ∧ p.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i))
    (hoff : ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v →
      (a = I.mu0 ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) ((k' β)⁻¹ * k β) = 1)
    (hT : ∀ β (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i →
      HasRes P.1 (adAt B.host.F P.1 ((((k' β)⁻¹ * k β)⁻¹ : TC.GA B (B.R.N i)).1 r j))
        (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)) :
    I.Reads u a i chOf Lb U' chi' (fun c => y c * k' (chOf c)) st (fun β => (k' β)⁻¹ * k β) where
  key := R.key
  onto := R.onto
  lb := R.lb
  k_std := hstd
  k_off := hoff
  k_T := hT
  pt := fun c => by
    have e : y c * k' (chOf c) * ((k' (chOf c))⁻¹ * k (chOf c)) = y c * k (chOf c) := by group
    rw [e]
    exact R.pt c
  lev := fun c x q hq => by
    have e : y c * k' (chOf c) * x * ((k' (chOf c))⁻¹ * k (chOf c)) = y c * (k' (chOf c) * x * (k' (chOf c))⁻¹) * k (chOf c) := by
      group
    rw [e] at hq
    exact (hU (chOf c) x).trans (R.lev c _ q hq)
  chr := fun c x κ hκ hq => by
    have e : y c * k' (chOf c) * x.1 * ((k' (chOf c))⁻¹ * k (chOf c)) =
        y c * (k' (chOf c) * x.1 * (k' (chOf c))⁻¹) * k (chOf c) := by group
    rw [e] at hq
    rw [hchi]
    exact R.chr c _ κ hκ hq
  stab := R.stab

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

/- English proof (translation)
Take `⟨k₁, hk₁U, h1, h2⟩` from `GlobalTheory.TwU.MoveOff.exists_one_on σ J hSf.toFinset k hkU`. Establish `e1 : ∀ v ∈ Sp, bc (prV (E` using `E) v) (k * k₁⁻¹) = bc (prV (E := E) v) k := fun v hv => by`. Rewrite using `[map_mul, map_inv, h1 v (hSf.mem_toFinset.2 hv), inv_one, mul_one]`. Establish `e2 : ∀ v ∉ Sp, bc (prV (E` using `E) v) (k * k₁⁻¹) = 1 := fun v hv => by`. Rewrite using `[map_mul, map_inv, h2 v (fun h => hv (hSf.mem_toFinset.1 h)), mul_inv_cancel]`.

Use `⟨⟨k * k₁⁻¹, (mem_basePts_iff _ _).2 ⟨mul_mem hkU (inv_mem hk₁U), fun v => ?_, fun v hv => ?_⟩⟩, e1, e2⟩` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ Sp`. Rewrite using `[e1 v hv]`. Conclude with `hkV v`. Rewrite using `[e2 v hv]`.

Conclude with `one_mem _`. Conclude with `e2 v fun h => hST v h hv`.
-/
theorem exists_basePt_on (S : StepLevel F E σ J T f bad) (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hkU : k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hkV : ∀ v, bc (prV (E := E) v) k ∈ levelVL σ J v S.Lb)
    (Sp : Set (HeightOneSpectrum (𝓞 F))) (hSf : Sp.Finite) (hST : ∀ v ∈ Sp, (T : 𝓞 F) ∉ v.asIdeal) :
    ∃ w : basePts S, (∀ v ∈ Sp, bc (prV (E := E) v) w.1 = bc (prV (E := E) v) k) ∧ ∀ v ∉ Sp, bc (prV (E := E) v) w.1 = 1 := by
  obtain ⟨k₁, hk₁U, h1, h2⟩ := GlobalTheory.TwU.MoveOff.exists_one_on σ J hSf.toFinset k hkU
  have e1 : ∀ v ∈ Sp, bc (prV (E := E) v) (k * k₁⁻¹) = bc (prV (E := E) v) k := fun v hv => by
    rw [map_mul, map_inv, h1 v (hSf.mem_toFinset.2 hv), inv_one, mul_one]
  have e2 : ∀ v ∉ Sp, bc (prV (E := E) v) (k * k₁⁻¹) = 1 := fun v hv => by
    rw [map_mul, map_inv, h2 v (fun h => hv (hSf.mem_toFinset.1 h)), mul_inv_cancel]
  refine ⟨⟨k * k₁⁻¹, (mem_basePts_iff _ _).2 ⟨mul_mem hkU (inv_mem hk₁U), fun v => ?_, fun v hv => ?_⟩⟩, e1, e2⟩
  · by_cases hv : v ∈ Sp
    · rw [e1 v hv]
      exact hkV v
    · rw [e2 v hv]
      exact one_mem _
  · exact e2 v fun h => hST v h hv

end Gen

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `R` using `hA.reads i hi`. Establish `hPr` using `l.pr`. Establish `hX` using `GlobalTheory.Mem.FieldsLaws.fields_ok B`. Use `haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩`. Establish `hgr : gramN (I.rec7 l Z) i hi = 1` using `((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1`.

Establish `hB` using `basePi_of_ok hX hPr u`. Establish `hLb : (A.K i hi β).lev.Lb = baseLb B.fields.E (B.R.N i) ((B.primes X).vT u)`. Use extensionality with `x`. Conclude with `(R.lb β x).trans (GlobalTheory.Mem.Col2.Reside.mem_baseLb hPr u _ x).symm`. Establish `k3 : ∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i → HasRes P.1 (adAt B.host.F P.1 (((A.kb i β)⁻¹ : TC.GA B (B.R.N i)).1 r j)) (if j = r then ((diaT (Pr` using `B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) else 0) := fun P r j hr => by`.

Establish `hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u)))`. Establish `h0 : Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u)) ≠ 0` using `fun h0 => hB.conj_notMem P.2 (Ideal.Quotient.eq_zero_iff_mem.1 h0)`. Conclude with `@Ne.isUnit (Res P.1) _ _ h0`. Establish `e : ((diaT (Pr` using `B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) := by`. Unfold `diaT`.

Rewrite using `[dif_pos hu]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `R.k_T β P r j hr`. Take `⟨hkU, hkV, -, -⟩` from `GlobalTheory.T.admissibleBasePoint_unitary_normalisesLevel B.sp.cm (B.R.N i) hB (A.kb i β) (diaT (Pr := B.primes X) u) (R.k_std β) k3`.

Use `exists_basePt_on (A.K i hi β).lev (A.kb i β) ?_ (fun v => ?_) S hSf hST` and prove the remaining obligations. Rewrite using `[hgr]`. Conclude with `hkU`. Rewrite using `[hLb, hgr]`. Conclude with `hkV v`.
-/
theorem exists_mv {I : TC B X} (hI : I.Ok) (hP : TC.Pins B X) {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i)
    (S : Set (HeightOneSpectrum (𝓞 B.host.F))) (hSf : S.Finite) (hST : ∀ v ∈ S, (B.T u : 𝓞 B.host.F) ∉ v.asIdeal) :
    ∃ w : basePts (A.K i hi β).lev, (∀ v ∈ S, bc (prV (E := B.host.E) v) w.1 = bc (prV (E := B.host.E) v) (A.kb i β)) ∧
      ∀ v ∉ S, bc (prV (E := B.host.E) v) w.1 = 1 := by
  have R := hA.reads i hi
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hgr : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have hB := basePi_of_ok hX hPr u
  have hLb : (A.K i hi β).lev.Lb = baseLb B.fields.E (B.R.N i) ((B.primes X).vT u) := by
    ext x
    exact (R.lb β x).trans (GlobalTheory.Mem.Col2.Reside.mem_baseLb hPr u _ x).symm
  have k3 : ∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i →
      HasRes P.1 (adAt B.host.F P.1 (((A.kb i β)⁻¹ : TC.GA B (B.R.N i)).1 r j))
      (if j = r then ((diaT (Pr := B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) else 0) :=
    fun P r j hr => by
    have hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u))) := by
      have h0 : Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u)) ≠ 0 := fun h0 =>
        hB.conj_notMem P.2 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      exact @Ne.isUnit (Res P.1) _ _ h0
    have e : ((diaT (Pr := B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) =
        Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) := by
      unfold diaT
      rw [dif_pos hu]
      rfl
    rw [e]
    exact R.k_T β P r j hr
  obtain ⟨hkU, hkV, -, -⟩ := GlobalTheory.T.admissibleBasePoint_unitary_normalisesLevel B.sp.cm (B.R.N i) hB (A.kb i β) (diaT (Pr := B.primes X) u) (R.k_std β) k3
  refine exists_basePt_on (A.K i hi β).lev (A.kb i β) ?_ (fun v => ?_) S hSf hST
  · rw [hgr]
    exact hkU
  · rw [hLb, hgr]
    exact hkV v

section Pt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {hc : CMData F E} {n : ℕ}

/- English proof (translation)
Establish `h1 : (Pi.single j 1 : Fin n → AfE F E) ∈ latS (F` using `F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n) := by`. Use `(Formalism.L2.Col.mem_latS_std _).2 fun r => ?_` and prove the remaining obligations. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Establish `h2` using `(Formalism.L2.Col.mem_latS_std _).1 ((h _).1 h1) i`. Rewrite `h2` using `[Matrix.mulVec_single_one]`. Conclude with `h2`.
-/
theorem rInt_of_stab {m : GL (Fin n) (AfE F E)}
    (h : m ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))
      (Formalism.L2.Col.stdLat E n))) (i j : Fin n) : (m : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E := by
  have h1 : (Pi.single j 1 : Fin n → AfE F E) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n) := by
    refine (Formalism.L2.Col.mem_latS_std _).2 fun r => ?_
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have h2 := (Formalism.L2.Col.mem_latS_std _).1 ((h _).1 h1) i
  rw [Matrix.mulVec_single_one] at h2
  exact h2

end Pt

section Pt2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {hc : CMData F E} {n : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

/- English proof (translation)
Apply `GlobalTheory.Mem.Col2.ChTwRead.adAt_congr_prV` to reduce the goal to its premises. Conclude with `congrArg (fun g : GL (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F) => g.1 i j) e`.
-/
theorem adAt_congr_bc {P : HeightOneSpectrum (𝓞 E)} {x y : GL (Fin n) (AfE F E)}
    (e : bc (prV (E := E) (P.under (𝓞 F))) x = bc (prV (E := E) (P.under (𝓞 F))) y) (i j : Fin n) :
    adAt F P ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j) = adAt F P ((y : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
  apply GlobalTheory.Mem.Col2.ChTwRead.adAt_congr_prV
  exact congrArg (fun g : GL (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F) => g.1 i j) e

/- English proof (translation)
Use `set m := k₁⁻¹ * k with hm`. Establish `em1 : ∀ v ∈ S, bc (prV (E` using `E) v) m = bc (prV (E := E) v) k := fun v hv => by`. Rewrite using `[hm, map_mul, map_inv, hS v hv, inv_one, one_mul]`. Establish `em2 : ∀ v ∉ S, bc (prV (E` using `E) v) m = 1 := fun v hv => by`. Rewrite using `[hm, map_mul, map_inv, hS' v hv, inv_mul_cancel]`.

Use `haveI := GlobalTheory.TwU.MoveOff.stdLat_finite (E := E) n`. Establish `hks : k⁻¹ ∈ stabGL (latS (F` using `F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := hkl`. Establish `hms : m⁻¹ ∈ stabGL (latS (F` using `F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := by`. Use `GlobalTheory.TwU.MoveOff.mem_stab_of_local _ _ _ hks fun v => ?_` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ S`.

Use `left`. Rewrite using `[map_inv, map_inv, em1 v hv]`. Use `right`. Rewrite using `[map_inv, em2 v hv, inv_one]`. Establish `hmU : m ∈ Formalism.L2.Herm.UstdAf hc n` using `mul_mem (inv_mem hk₁) hkU`.

Establish `h1 : ∀ i j, (m : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E` using `rInt_of_stab (by simpa using inv_mem hms)`. Establish `h2 : ∀ i j, ((m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E` using `rInt_of_stab hms`. Establish `hT : ∀ P ∈ ST, ∀ i j, adAt F P ((m : Matrix (Fin n) (Fin n) (AfE F E)) i j) = adAt F P (((1 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j)` using `fun P hP i j => adAt_congr_bc (by rw [em2 _ (hST P hP), map_one]) i j`. Establish `hh : ∀ w : SG, LevRead.IsRed w.1 m ((1 : GLG E n SG) w)` using `fun w => by show LevRead.IsRed w.1 m ((1 : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal))`. Rewrite using `[Units.val_one]`.

Distinguish the cases in `hw : w.1.under (𝓞 F) ∈ S`. Conclude with `(hSG w.1 w.2 hw).congr rfl (em1 _ hw).symm`. Conclude with `LevRead.isRed_one.congr rfl (by rw [em2 _ hw, map_one])`. Establish `hfr : ∀ (P : Q) (i j : Fin n), adAt F P.1 (((g * k * m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ ((p.fr P * (((1 : GLQ E n Q) P)⁻¹ : GLint E n P.1).1) (Pi.single j 1) i)` using `fun P i j => by`. Establish `e : bc (prV (E` using `E) (P.1.under (𝓞 F))) (g * k * m⁻¹) = bc (prV (E := E) (P.1.under (𝓞 F))) (g * k) := by`.

Rewrite using `[map_mul (bc _) (g * k), map_inv, em2 _ (hQ P.1 P.2), inv_one, mul_one]`. Rewrite using `[adAt_congr_bc e i j, hp.fr P i j]`. Both sides reduce to the same expression. Establish `H` using `LevLiftPt.isPtOf_mul_fr hp hmU h1 h2 hT hh 1 hfr`. Establish `e1 : g * k * m⁻¹ = g * k₁` using `by rw [hm]; group`.

Establish `e2 : ((1, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p = p` using `one_smul _ p`. Rewrite `H` using `[e1, e2]`. Conclude with `H`.
-/
theorem isPtOf_move (S : Set (HeightOneSpectrum (𝓞 F))) {g k k₁ : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q}
    (hp : IsPtOf hc (g * k) p) (hkU : k ∈ Formalism.L2.Herm.UstdAf hc n)
    (hkl : Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n)) (hk₁ : k₁ ∈ Formalism.L2.Herm.UstdAf hc n)
    (hS : ∀ v ∈ S, bc (prV (E := E) v) k₁ = 1) (hS' : ∀ v ∉ S, bc (prV (E := E) v) k₁ = bc (prV (E := E) v) k)
    (hST : ∀ P ∈ ST, P.under (𝓞 F) ∉ S) (hQ : ∀ P ∈ Q, P.under (𝓞 F) ∉ S)
    (hSG : ∀ w ∈ SG, w.under (𝓞 F) ∈ S → LevRead.IsRed w k 1) : IsPtOf hc (g * k₁) p := by
  classical
  set m := k₁⁻¹ * k with hm
  have em1 : ∀ v ∈ S, bc (prV (E := E) v) m = bc (prV (E := E) v) k := fun v hv => by
    rw [hm, map_mul, map_inv, hS v hv, inv_one, one_mul]
  have em2 : ∀ v ∉ S, bc (prV (E := E) v) m = 1 := fun v hv => by
    rw [hm, map_mul, map_inv, hS' v hv, inv_mul_cancel]
  haveI := GlobalTheory.TwU.MoveOff.stdLat_finite (E := E) n
  have hks : k⁻¹ ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := hkl
  have hms : m⁻¹ ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := by
    refine GlobalTheory.TwU.MoveOff.mem_stab_of_local _ _ _ hks fun v => ?_
    by_cases hv : v ∈ S
    · left
      rw [map_inv, map_inv, em1 v hv]
    · right
      rw [map_inv, em2 v hv, inv_one]
  have hmU : m ∈ Formalism.L2.Herm.UstdAf hc n := mul_mem (inv_mem hk₁) hkU
  have h1 : ∀ i j, (m : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E := rInt_of_stab (by simpa using inv_mem hms)
  have h2 : ∀ i j, ((m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E := rInt_of_stab hms
  have hT : ∀ P ∈ ST, ∀ i j, adAt F P ((m : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      adAt F P (((1 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) := fun P hP i j =>
    adAt_congr_bc (by rw [em2 _ (hST P hP), map_one]) i j
  have hh : ∀ w : SG, LevRead.IsRed w.1 m ((1 : GLG E n SG) w) := fun w => by
    show LevRead.IsRed w.1 m ((1 : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal))
    rw [Units.val_one]
    by_cases hw : w.1.under (𝓞 F) ∈ S
    · exact (hSG w.1 w.2 hw).congr rfl (em1 _ hw).symm
    · exact LevRead.isRed_one.congr rfl (by rw [em2 _ hw, map_one])
  have hfr : ∀ (P : Q) (i j : Fin n), adAt F P.1 (((g * k * m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      algebraMap E _ ((p.fr P * (((1 : GLQ E n Q) P)⁻¹ : GLint E n P.1).1) (Pi.single j 1) i) := fun P i j => by
    have e : bc (prV (E := E) (P.1.under (𝓞 F))) (g * k * m⁻¹) = bc (prV (E := E) (P.1.under (𝓞 F))) (g * k) := by
      rw [map_mul (bc _) (g * k), map_inv, em2 _ (hQ P.1 P.2), inv_one, mul_one]
    rw [adAt_congr_bc e i j, hp.fr P i j]
    rfl
  have H := LevLiftPt.isPtOf_mul_fr hp hmU h1 h2 hT hh 1 hfr
  have e1 : g * k * m⁻¹ = g * k₁ := by rw [hm]; group
  have e2 : ((1, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p = p := one_smul _ p
  rw [e1, e2] at H
  exact H

/- English proof (translation)
Take `⟨p, hp, hN⟩` from `h`. Use `⟨p, ⟨mul_mem (inv_mem hwU) hp.uni, ?_, fun P => absurd P.2 (Finset.notMem_empty _), fun P => absurd P.2 (Finset.notMem_empty _), fun P => absurd P.2 (Finset.notMem_empty _)⟩, hN⟩` and prove the remaining obligations. Establish `hl` using `hp.lat`. Rewrite `hl`, the goal using `[hN]`. Use `haveI := GlobalTheory.TwU.MoveOff.stdLat_finite (E := E) n`.

Establish `hs : k⁻¹ ∈ stabGL (latS (F` using `F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := hl`. Establish `key : (w⁻¹ * k)⁻¹ ∈ stabGL (latS (F` using `F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := by`. Use `GlobalTheory.TwU.MoveOff.mem_stab_of_local _ _ _ hs fun v => ?_` and prove the remaining obligations. Break down `hloc v with e | e` into its components or cases. Use `right`.

Rewrite using `[map_inv, map_mul, map_inv, e, inv_mul_cancel, inv_one]`. Use `left`. Rewrite using `[map_inv, map_mul, map_inv, e, inv_one, one_mul, map_inv]`. Conclude with `key`.
-/
theorem std_move' (k w : GL (Fin n) (AfE F E)) (hwU : w ∈ Formalism.L2.Herm.UstdAf hc n)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      bc (prV (E := E) v) w = bc (prV (E := E) v) k ∨ bc (prV (E := E) v) w = 1)
    (h : ∃ p : DecoF E n ∅ ∅ ∅, IsPtOf hc k p ∧ p.deco.1.N = Formalism.L2.Col.stdLat E n) :
    ∃ p : DecoF E n ∅ ∅ ∅, IsPtOf hc (w⁻¹ * k) p ∧ p.deco.1.N = Formalism.L2.Col.stdLat E n := by
  obtain ⟨p, hp, hN⟩ := h
  refine ⟨p, ⟨mul_mem (inv_mem hwU) hp.uni, ?_, fun P => absurd P.2 (Finset.notMem_empty _),
    fun P => absurd P.2 (Finset.notMem_empty _), fun P => absurd P.2 (Finset.notMem_empty _)⟩, hN⟩
  have hl := hp.lat
  rw [hN] at hl ⊢
  haveI := GlobalTheory.TwU.MoveOff.stdLat_finite (E := E) n
  have hs : k⁻¹ ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := hl
  have key : (w⁻¹ * k)⁻¹ ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := by
    refine GlobalTheory.TwU.MoveOff.mem_stab_of_local _ _ _ hs fun v => ?_
    rcases hloc v with e | e
    · right
      rw [map_inv, map_mul, map_inv, e, inv_mul_cancel, inv_one]
    · left
      rw [map_inv, map_mul, map_inv, e, inv_one, one_mul, map_inv]
  exact key

end Pt2

section Red

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {n : ℕ}

/- English proof (translation)
Establish `hks : k⁻¹ ∈ stabGL (latS (F` using `F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := hkl`. Establish `hk : k ∈ stabGL (latS (F` using `F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := by`. Simplify using `using inv_mem hks`. Conclude with `⟨(mem_rInt_iff F E _).1 (rInt_of_stab hk i j) P, (mem_rInt_iff F E _).1 (rInt_of_stab hks i j) P⟩`.
-/
theorem val_le_one_of_carries {k : GL (Fin n) (AfE F E)}
    (hkl : Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n)) (P : HeightOneSpectrum (𝓞 E)) (i j : Fin n) :
    Valued.v (adAt F P ((k : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1 ∧
      Valued.v (adAt F P (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1 := by
  have hks : k⁻¹ ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := hkl
  have hk : k ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := by
    simpa using inv_mem hks
  exact ⟨(mem_rInt_iff F E _).1 (rInt_of_stab hk i j) P, (mem_rInt_iff F E _).1 (rInt_of_stab hks i j) P⟩

/- English proof (translation)
Take `⟨A, hA⟩` from `LevRead.exists_isRed (P := P) (x := k) (fun i j => (val_le_one_of_carries hkl P i j).1) (fun i j => (val_le_one_of_carries hkl P i j).2)`. Establish `h1` using `hA.mul h`. Rewrite `h1` using `[mul_inv_cancel, mul_one]`. Rewrite `hA` using `[h1.unique LevRead.isRed_one]`. Conclude with `hA`.
-/
theorem isRed_one_of_inv {P : HeightOneSpectrum (𝓞 E)} {k : GL (Fin n) (AfE F E)}
    (hkl : Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n)) (h : LevRead.IsRed P k⁻¹ 1) :
    LevRead.IsRed P k 1 := by
  obtain ⟨A, hA⟩ := LevRead.exists_isRed (P := P) (x := k) (fun i j => (val_le_one_of_carries hkl P i j).1)
    (fun i j => (val_le_one_of_carries hkl P i j).2)
  have h1 := hA.mul h
  rw [mul_inv_cancel, mul_one] at h1
  rw [h1.unique LevRead.isRed_one] at hA
  exact hA

end Red

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `w hw`. Establish `hPr` using `(base_fields_primes_ok B X).2.1`. Establish `hN` using `N_m_succ B.R`. Establish `hq` using `(GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away I hI).2 u a`. Take `⟨k0, h1, h2, h3⟩` from `GlobalTheory.Mem.Col2.BasePoint.exists_kStd X hPr u (B.R.N B.R.m)`.

Take `⟨t, t1, t2, t3⟩` from `GlobalTheory.Mem.Col2.TwUnit.exists_tw B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (fun P hP => (hq P hP).1) (X.piT u) (fun P hP => (hq P hP).2.1)`. Establish `hks : I.TopPt l Z u a (k0 * t)` using `fun d g' g hd he => GlobalTheory.Mem.Col2.TilQ.pt_tilF_gen I hI hP l Z u a k0 t h1 h2 h3 t1 t2 d g' g hd he`. Establish `hp` using `GlobalTheory.Mem.Col2.TopPtModel.topPt_base I l Z h`. Establish `hp'` using `GlobalTheory.Mem.Col2.TopPtModel.topPt_base I l Z hks`. Establish `hgw : ∃ i, ((B.primes X).g i : 𝓞 B.fields.E) ∈ w.asIdeal`.

Establish `h1 : ∃ i, w ∈ (B.primes X).vG i`. Establish `h0` using `hw`. Unfold `Primes.vGs at h0`. Simplify using `only [Finset.mem_union] at h0`. Break down `h0 with h | h` into its components or cases.

Use `exacts [⟨0, h⟩, ⟨1, h⟩]`. Take `⟨i, hi⟩` from `h1`. Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[← hPr.piG_norm i]`. Conclude with `w.asIdeal.mul_mem_left _ (mem_of_mem_divs hi)`.

Establish `hTw : (B.T u : 𝓞 B.host.F) ∉ (w.under (𝓞 B.host.F)).asIdeal`. Introduce `hT`. Take `⟨i, hi⟩` from `hgw`. Establish `h1 : ((B.primes X).T u : 𝓞 B.fields.E) ∈ w.asIdeal`. Establish `h2 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ w.asIdeal` using `hT`.

Rewrite `h2` using `[map_natCast]`. Conclude with `h2`. Establish `hc : Nat.Coprime ((B.primes X).T u) ((B.primes X).g i)` using `(Nat.coprime_primes (hPr.T_prime u) (hPr.g_prime i)).2 (hPr.T_ne_g u i)`. Establish `h3 : ((1 : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal`. Take `⟨a, b, hab⟩` from `(Nat.isCoprime_iff_coprime.2 hc)`.

Establish `e : ((1 : ℤ) : 𝓞 B.fields.E) = (a : 𝓞 B.fields.E) * ((B.primes X).T u : 𝓞 B.fields.E) + (b : 𝓞 B.fields.E) * ((B.primes X).g i : 𝓞 B.fields.E)`. Rewrite using `[← hab]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e' : ((1 : ℕ) : 𝓞 B.fields.E) = ((1 : ℤ) : 𝓞 B.fields.E)` using `by simp`.

Rewrite using `[e', e]`. Conclude with `add_mem (w.asIdeal.mul_mem_left _ h1) (w.asIdeal.mul_mem_left _ hi)`. Conclude with `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h3))`. Establish `hk0 : k0.1.map (adAt B.host.F w) = 1` using `GlobalTheory.Mem.Col2.TopPtModel.adAt_of_prV w (h2 _ hTw)`. Establish `hwQ : w ∉ I.Q a` using `fun h => (hq w h).1.2.1 hw`.

Establish `hwQ' : conjPrime₂ w ∉ I.Q a` using `fun h => (hq _ h).1.2.2.2.1 (by rw [CharValCompare.conjP_conjP]; exact hw)`. Establish `ht : t.1.map (adAt B.host.F w) = 1` using `Matrix.ext fun i j => (t3 w hwQ hwQ' i j).trans Matrix.one_apply.symm`. Use `set m : TC.GA B (B.R.N B.R.m) := k⁻¹ * (k0 * t) with hm`. Establish `em : ∀ i j, adAt B.host.F w (m.1 i j) = adAt B.host.F w ((k⁻¹ : TC.GA B (B.R.N B.R.m)).1 i j)` using `fun i j => by`. Establish `e` using `GlobalTheory.Mem.Col2.TopPtModel.adAt_mul w k⁻¹ (k0 * t)`.

Rewrite `e` using `[GlobalTheory.Mem.Col2.TopPtModel.adAt_mul w k0 t, hk0, ht, mul_one, mul_one]`. Conclude with `congrFun (congrFun e i) j`. Take `⟨A, hA⟩` from `LevRead.exists_isRed (P := w) (x := k⁻¹) (fun i j => (val_le_one_of_carries hkl w i j).2) (fun i j => by rw [inv_inv]; exact (val_le_one_of_carries hkl w i j).1)`. Establish `hA' : LevRead.IsRed w m A` using `fun i j => by rw [em]; exact hA i j`. Establish `e1 : k0 * t * m⁻¹ = k` using `by rw [hm]; group`.

Establish `hq' : IsPtOf B.sp.cm (k0 * t * m⁻¹) (((1, 1, 1) : UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m) (QE I.sel (I.tup a))) • tilF I.sel (I.tup a) u (DecoF.base B.fields.E (B.R.N B.R.m - 1) ∅ (B.primes X).vGs (QE I.sel (I.tup …`. Rewrite using `[e1, show ((1, 1, 1) : UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m) (QE I.sel (I.tup a))) = 1 from rfl, one_smul]`. Conclude with `hp`. Establish `e2` using `LevRead.eq_red hp' hq' ⟨w, hw⟩ hA'`. Establish `e3 : (A : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (𝓞 B.fields.E ⧸ w.asIdeal)) = 1` using `by rw [e2]; rfl`.

Rewrite `hA` using `[e3]`. Conclude with `isRed_one_of_inv hkl hA`.
-/
theorem isRed_one_of_topPt (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (k : TC.GA B (B.R.N B.R.m))
    (hkl : Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat B.host.E (B.R.N B.R.m)) (Formalism.L2.Col.stdLat B.host.E (B.R.N B.R.m)))
    (h : I.TopPt l Z u a k) : ∀ w ∈ (B.primes X).vGs, LevRead.IsRed w k 1 := by
  intro w hw
  have hPr := (base_fields_primes_ok B X).2.1
  have hN := N_m_succ B.R
  have hq := (GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away I hI).2 u a
  obtain ⟨k0, h1, h2, h3⟩ := GlobalTheory.Mem.Col2.BasePoint.exists_kStd X hPr u (B.R.N B.R.m)
  obtain ⟨t, t1, t2, t3⟩ := GlobalTheory.Mem.Col2.TwUnit.exists_tw B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)
    (B.primes X).vGs (I.Q a) (fun P hP => (hq P hP).1) (X.piT u) (fun P hP => (hq P hP).2.1)
  have hks : I.TopPt l Z u a (k0 * t) := fun d g' g hd he =>
    GlobalTheory.Mem.Col2.TilQ.pt_tilF_gen I hI hP l Z u a k0 t h1 h2 h3 t1 t2 d g' g hd he
  have hp := GlobalTheory.Mem.Col2.TopPtModel.topPt_base I l Z h
  have hp' := GlobalTheory.Mem.Col2.TopPtModel.topPt_base I l Z hks

  have hgw : ∃ i, ((B.primes X).g i : 𝓞 B.fields.E) ∈ w.asIdeal := by
    have h1 : ∃ i, w ∈ (B.primes X).vG i := by
      have h0 := hw
      unfold Primes.vGs at h0
      simp only [Finset.mem_union] at h0
      rcases h0 with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    obtain ⟨i, hi⟩ := h1
    refine ⟨i, ?_⟩
    rw [← hPr.piG_norm i]
    exact w.asIdeal.mul_mem_left _ (mem_of_mem_divs hi)
  have hTw : (B.T u : 𝓞 B.host.F) ∉ (w.under (𝓞 B.host.F)).asIdeal := by
    intro hT
    obtain ⟨i, hi⟩ := hgw
    have h1 : ((B.primes X).T u : 𝓞 B.fields.E) ∈ w.asIdeal := by
      have h2 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ w.asIdeal := hT
      rw [map_natCast] at h2
      exact h2
    have hc : Nat.Coprime ((B.primes X).T u) ((B.primes X).g i) :=
      (Nat.coprime_primes (hPr.T_prime u) (hPr.g_prime i)).2 (hPr.T_ne_g u i)
    have h3 : ((1 : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc)
      have e : ((1 : ℤ) : 𝓞 B.fields.E) = (a : 𝓞 B.fields.E) * ((B.primes X).T u : 𝓞 B.fields.E) +
          (b : 𝓞 B.fields.E) * ((B.primes X).g i : 𝓞 B.fields.E) := by
        rw [← hab]; push_cast; ring
      have e' : ((1 : ℕ) : 𝓞 B.fields.E) = ((1 : ℤ) : 𝓞 B.fields.E) := by simp
      rw [e', e]
      exact add_mem (w.asIdeal.mul_mem_left _ h1) (w.asIdeal.mul_mem_left _ hi)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h3))

  have hk0 : k0.1.map (adAt B.host.F w) = 1 :=
    GlobalTheory.Mem.Col2.TopPtModel.adAt_of_prV w (h2 _ hTw)
  have hwQ : w ∉ I.Q a := fun h => (hq w h).1.2.1 hw
  have hwQ' : conjPrime₂ w ∉ I.Q a := fun h => (hq _ h).1.2.2.2.1 (by rw [CharValCompare.conjP_conjP]; exact hw)
  have ht : t.1.map (adAt B.host.F w) = 1 :=
    Matrix.ext fun i j => (t3 w hwQ hwQ' i j).trans Matrix.one_apply.symm
  set m : TC.GA B (B.R.N B.R.m) := k⁻¹ * (k0 * t) with hm
  have em : ∀ i j, adAt B.host.F w (m.1 i j) = adAt B.host.F w ((k⁻¹ : TC.GA B (B.R.N B.R.m)).1 i j) := fun i j => by
    have e := GlobalTheory.Mem.Col2.TopPtModel.adAt_mul w k⁻¹ (k0 * t)
    rw [GlobalTheory.Mem.Col2.TopPtModel.adAt_mul w k0 t, hk0, ht, mul_one, mul_one] at e
    exact congrFun (congrFun e i) j
  obtain ⟨A, hA⟩ := LevRead.exists_isRed (P := w) (x := k⁻¹) (fun i j => (val_le_one_of_carries hkl w i j).2)
    (fun i j => by rw [inv_inv]; exact (val_le_one_of_carries hkl w i j).1)
  have hA' : LevRead.IsRed w m A := fun i j => by rw [em]; exact hA i j
  have e1 : k0 * t * m⁻¹ = k := by rw [hm]; group
  have hq' : IsPtOf B.sp.cm (k0 * t * m⁻¹) (((1, 1, 1) : UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs ×
      GLQ B.fields.E (B.R.N B.R.m) (QE I.sel (I.tup a))) • tilF I.sel (I.tup a) u
        (DecoF.base B.fields.E (B.R.N B.R.m - 1) ∅ (B.primes X).vGs (QE I.sel (I.tup a)))) := by
    rw [e1, show ((1, 1, 1) : UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs ×
      GLQ B.fields.E (B.R.N B.R.m) (QE I.sel (I.tup a))) = 1 from rfl, one_smul]
    exact hp
  have e2 := LevRead.eq_red hp' hq' ⟨w, hw⟩ hA'
  have e3 : (A : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (𝓞 B.fields.E ⧸ w.asIdeal)) = 1 := by rw [e2]; rfl
  rw [e3] at hA
  exact isRed_one_of_inv hkl hA

/- English proof (translation)
Substitute `hn` using the available equality. Take `⟨g, hg, e⟩` from `GlobalTheory.DefFree.AdelCls.exists_fin V ⟨y.1, y.2⟩`. Conclude with `⟨g, hg, congrArg Units.val (congrArg Subtype.val e)⟩`.
-/
theorem exists_gfC {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (y : UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ g ∈ GfC V, GlobalTheory.AdForm.finM V hn g = y.1.1 := by
  subst hn
  obtain ⟨g, hg, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V ⟨y.1, y.2⟩
  exact ⟨g, hg, congrArg Units.val (congrArg Subtype.val e)⟩

section Move

variable {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type}

def mvEl (hI : I.Ok) (hP : TC.Pins B X) (A : TwDat I l Z u a Ch) (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) :
    basePts (A.K i hi β).lev :=
  if i = B.R.m then (exists_mv hI hP A hA i hi β (offPl I u a) (offPl_finite I u a) fun _ hv => hv.2.1).choose else 1

set_option maxHeartbeats 2000000 in
/- English proof (translation)
Distinguish the cases in `h : i = B.R.m`. Establish `hs` using `(exists_mv hI hP A hA i hi β (offPl I u a) (offPl_finite I u a) fun _ hv => hv.2.1).choose_spec`. Establish `e : mvEl hI hP A hA i hi β = (exists_mv hI hP A hA i hi β (offPl I u a) (offPl_finite I u a) fun _ hv => hv.2.1).choose` using `if_pos h`. Rewrite using `[e]`. Use `⟨fun v => ?_, hs.2, fun _ => hs.1, fun h' => absurd h h'⟩` and prove the remaining obligations.

Distinguish the cases in `hv : v ∈ offPl I u a`. Conclude with `Or.inl (hs.1 v hv)`. Conclude with `Or.inr (hs.2 v hv)`. Establish `e : mvEl hI hP A hA i hi β = 1` using `if_neg h`. Rewrite using `[e]`.

Conclude with `⟨fun v => Or.inr (map_one _), fun v _ => map_one _, fun h' => absurd h' h, fun _ => rfl⟩`.
-/
theorem mvEl_spec (hI : I.Ok) (hP : TC.Pins B X) (A : TwDat I l Z u a Ch) (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) :
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), bc (prV (E := B.host.E) v) (mvEl hI hP A hA i hi β).1 = bc (prV (E := B.host.E) v) (A.kb i β) ∨
      bc (prV (E := B.host.E) v) (mvEl hI hP A hA i hi β).1 = 1) ∧
    (∀ v ∉ offPl I u a, bc (prV (E := B.host.E) v) (mvEl hI hP A hA i hi β).1 = 1) ∧
    (i = B.R.m → ∀ v ∈ offPl I u a, bc (prV (E := B.host.E) v) (mvEl hI hP A hA i hi β).1 = bc (prV (E := B.host.E) v) (A.kb i β)) ∧
    (i ≠ B.R.m → mvEl hI hP A hA i hi β = 1) := by
  by_cases h : i = B.R.m
  · have hs := (exists_mv hI hP A hA i hi β (offPl I u a) (offPl_finite I u a) fun _ hv => hv.2.1).choose_spec
    have e : mvEl hI hP A hA i hi β =
        (exists_mv hI hP A hA i hi β (offPl I u a) (offPl_finite I u a) fun _ hv => hv.2.1).choose := if_pos h
    rw [e]
    refine ⟨fun v => ?_, hs.2, fun _ => hs.1, fun h' => absurd h h'⟩
    by_cases hv : v ∈ offPl I u a
    · exact Or.inl (hs.1 v hv)
    · exact Or.inr (hs.2 v hv)
  · have e : mvEl hI hP A hA i hi β = 1 := if_neg h
    rw [e]
    exact ⟨fun v => Or.inr (map_one _), fun v _ => map_one _, fun h' => absurd h' h, fun _ => rfl⟩

def mvLift (hI : I.Ok) (hP : TC.Pins B X) (A : TwDat I l Z u a Ch) (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i) :=
  (exists_gfC ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi)
    ⟨(mvEl hI hP A hA i hi β).1, ((mem_basePts_iff _ _).1 (mvEl hI hP A hA i hi β).2).1⟩).choose

/- English proof (translation)
The claim follows from `(exists_gfC ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) ⟨(mvEl hI hP A hA i hi β).1, ((mem_basePts_iff _ _).1 (mvEl hI hP A hA i hi β).2).1⟩).choose_spec`.
-/
theorem mvLift_spec (hI : I.Ok) (hP : TC.Pins B X) (A : TwDat I l Z u a Ch) (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) :
    mvLift hI hP A hA i hi β ∈ GfC _ ∧
      finM _ (rankN (I.rec7 l Z) i hi) (mvLift hI hP A hA i hi β) = (mvEl hI hP A hA i hi β).1.1 :=
  (exists_gfC ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi)
    ⟨(mvEl hI hP A hA i hi β).1, ((mem_basePts_iff _ _).1 (mvEl hI hP A hA i hi β).2).1⟩).choose_spec

end Move

section Move2

variable {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type}

def mvB (hI : I.Ok) (hP : TC.Pins B X) (A : TwDat I l Z u a Ch) (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) :
    TC.GA B (B.R.N i) :=
  (mvEl hI hP A hA i hi β).1

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `mvEl_spec hI hP A hA i hi β`. Conclude with `⟨h1, h2, h3, fun h => by rw [mvB, h4 h]; rfl⟩`.
-/
theorem mvB_spec (hI : I.Ok) (hP : TC.Pins B X) (A : TwDat I l Z u a Ch) (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) :
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), bc (prV (E := B.host.E) v) (mvB hI hP A hA i hi β) = bc (prV (E := B.host.E) v) (A.kb i β) ∨
      bc (prV (E := B.host.E) v) (mvB hI hP A hA i hi β) = 1) ∧
    (∀ v ∉ offPl I u a, bc (prV (E := B.host.E) v) (mvB hI hP A hA i hi β) = 1) ∧
    (i = B.R.m → ∀ v ∈ offPl I u a, bc (prV (E := B.host.E) v) (mvB hI hP A hA i hi β) = bc (prV (E := B.host.E) v) (A.kb i β)) ∧
    (i ≠ B.R.m → mvB hI hP A hA i hi β = 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := mvEl_spec hI hP A hA i hi β
  exact ⟨h1, h2, h3, fun h => by rw [mvB, h4 h]; rfl⟩

def mvG (hI : I.Ok) (hP : TC.Pins B X) (A : TwDat I l Z u a Ch) (hA : A.Is) (i : ℕ) (β : Ch i) : TC.GA B (B.R.N i) :=
  if hi : i ≤ B.R.m then mvB hI hP A hA i hi β else 1

def mvW (hI : I.Ok) (hP : TC.Pins B X) (A : TwDat I l Z u a Ch) (hA : A.Is) (i : ℕ) (β : Ch i) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i) :=
  if hi : i ≤ B.R.m then mvLift hI hP A hA i hi β else 1

/- English proof (translation)
The claim follows from `dif_pos hi`.
-/
theorem mvG_eq (hI : I.Ok) (hP : TC.Pins B X) (A : TwDat I l Z u a Ch) (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) :
    mvG hI hP A hA i β = mvB hI hP A hA i hi β := dif_pos hi

/- English proof (translation)
Establish `e : mvW hI hP A hA i β = mvLift hI hP A hA i hi β` using `dif_pos hi`. Rewrite using `[e]`. Conclude with `mvLift_spec hI hP A hA i hi β`.
-/
theorem mvW_spec (hI : I.Ok) (hP : TC.Pins B X) (A : TwDat I l Z u a Ch) (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) :
    mvW hI hP A hA i β ∈ GfC _ ∧
      finM _ (rankN (I.rec7 l Z) i hi) (mvW hI hP A hA i β) = (mvEl hI hP A hA i hi β).1.1 := by
  have e : mvW hI hP A hA i β = mvLift hI hP A hA i hi β := dif_pos hi
  rw [e]
  exact mvLift_spec hI hP A hA i hi β

set_option maxHeartbeats 2000000 in

def moved (hI : I.Ok) (hP : TC.Pins B X) (A : TwDat I l Z u a Ch) (hA : A.Is) : TwDat I l Z u a Ch where
  bad := A.bad
  chOf := A.chOf
  K i hi β := moveChart (A.K i hi β) (mvEl hI hP A hA i hi β)
  kb i β := (mvG hI hP A hA i β)⁻¹ * A.kb i β
  kA i β := (mvW hI hP A hA i β)⁻¹ * A.kA i β
  xr i β := (GlobalTheory.Mem.WeilTwist.exists_isDetRoot _ ((mvW hI hP A hA i β)⁻¹ * A.kA i β)).choose
  b0 := A.b0
  p0 := A.p0
  U i β := (A.U i β).comap (MulAut.conj (mvW hI hP A hA i β)).toMonoidHom
  chi i β := (A.chi i β).comp ((MulAut.conj (mvW hI hP A hA i β)).toMonoidHom.subgroupComap (A.U i β))
  h i β c := A.h i β c * mvW hI hP A hA i β
  chr := A.chr
  e := A.e

end Move2

section Is

variable {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type}

/- English proof (translation)
Establish `h1` using `(rls_vT_iff (GlobalTheory.Mem.FieldsLaws.fields_ok B) hPr u P).1 hP`. Establish `h2 : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal`. Rewrite using `[← hPr.piT_norm u]`. Conclude with `P.asIdeal.mul_mem_right _ h1`. Use `show algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ P.asIdeal`.

Rewrite using `[map_natCast]`. Conclude with `h2`.
-/
theorem T_mem_of_vT (hPr : (B.primes X).Ok) (u : B.Word) {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ (B.primes X).vT u) :
    (B.T u : 𝓞 B.host.F) ∈ (P.under (𝓞 B.host.F)).asIdeal := by
  have h1 := (rls_vT_iff (GlobalTheory.Mem.FieldsLaws.fields_ok B) hPr u P).1 hP
  have h2 : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
    rw [← hPr.piT_norm u]
    exact P.asIdeal.mul_mem_right _ h1
  show algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ P.asIdeal
  rw [map_natCast]
  exact h2

/- English proof (translation)
Introduce and unpack `⟨⟨j, hj⟩, -, -⟩`. Take `⟨a', -, ha'⟩` from `Finset.mem_biUnion.1 hP`. Establish `hq` using `((GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away I hI).2 u a' P ha').1`. Establish `hov : Formalism.L2.Host.OverP B.host (B.host.g j) P` using `by show ((B.host.g j : ℕ) : 𝓞 B.host.E) ∈ P.asIdeal`. Establish `: algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.host.g j : 𝓞 B.host.F) ∈ P.asIdeal` using `hj`.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Break down `(GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1.cover j P hov with h | h` into its components or cases. Conclude with `hq.2.1 h`. Conclude with `hq.2.2.2.1 h`.
-/
theorem not_offPl_SQ (hI : I.Ok) {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ I.SQ) : P.under (𝓞 B.host.F) ∉ offPl I u a := by
  rintro ⟨⟨j, hj⟩, -, -⟩
  obtain ⟨a', -, ha'⟩ := Finset.mem_biUnion.1 hP
  have hq := ((GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away I hI).2 u a' P ha').1
  have hov : Formalism.L2.Host.OverP B.host (B.host.g j) P := by
    show ((B.host.g j : ℕ) : 𝓞 B.host.E) ∈ P.asIdeal
    have : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.host.g j : 𝓞 B.host.F) ∈ P.asIdeal := hj
    rwa [map_natCast] at this
  rcases (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1.cover j P hov with h | h
  · exact hq.2.1 h
  · exact hq.2.2.2.1 h

/- English proof (translation)
Establish `e1 : finM V hn W * finM V hn W⁻¹ = 1`. Rewrite using `[← GlobalTheory.AdForm.StabMove.finM_mul, mul_inv_cancel, GlobalTheory.AdForm.Model.finM_one]`. Rewrite `e1` using `[h]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`.

Use `_ = (w⁻¹ : GL (Fin n) (EF D)).1 * (w.1 * finM V hn W⁻¹) := Matrix.mul_assoc _ _ _`. Use `_ = (w⁻¹ : GL (Fin n) (EF D)).1 := by rw [e1, Matrix.mul_one]`.
-/
theorem finM_inv_of {D : D7} {V : HSp D} {n : ℕ} {hn : V.rank = n} {W : GA D V} {w : GL (Fin n) (EF D)}
    (h : finM V hn W = w.1) : finM V hn W⁻¹ = (w⁻¹ : GL (Fin n) (EF D)).1 := by
  have e1 : finM V hn W * finM V hn W⁻¹ = 1 := by
    rw [← GlobalTheory.AdForm.StabMove.finM_mul, mul_inv_cancel, GlobalTheory.AdForm.Model.finM_one]
  rw [h] at e1
  calc finM V hn W⁻¹ = ((w⁻¹ : GL (Fin n) (EF D)).1 * w.1) * finM V hn W⁻¹ := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    _ = (w⁻¹ : GL (Fin n) (EF D)).1 * (w.1 * finM V hn W⁻¹) := Matrix.mul_assoc _ _ _
    _ = (w⁻¹ : GL (Fin n) (EF D)).1 := by rw [e1, Matrix.mul_one]

end Is

section Main

variable {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type}

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Establish `hPr` using `l.pr`. Establish `wU : ∀ i (hi : i ≤ B.R.m) β, mvB hI hP A hA i hi β ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i)`. Introduce `i hi β`. Establish `hgr : gramN (I.rec7 l Z) i hi = 1` using `((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1`. Establish `h : mvB hI hP A hA i hi β ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)` using `((mem_basePts_iff _ _).1 (mvEl hI hP A hA i hi β).2).1`.

Establish `h2` using `GlobalTheory.TwU.AtTrue.mem_UPts_one hgr h`. Conclude with `h2`. Establish `hkb : ∀ i (hi : i ≤ B.R.m), (moved hI hP A hA).kb i = fun β => (mvB hI hP A hA i hi β)⁻¹ * A.kb i β` using `fun i hi => funext fun β => by show (mvG hI hP A hA i β)⁻¹ * A.kb i β = _`. Rewrite using `[mvG_eq hI hP A hA i hi β]`. Use `⟨fun i hi => ?_, fun β => ?_, fun i hi β => ?_, fun i hi β => ?_, fun i hi c => hA.rep i hi c, fun i hi β g => ?_, fun i hi β g κ hκ => ?_, fun i hi β c => ?_, hA.chr, hA.idem, fun i hi β => ?_, hA.bad_le⟩` and prove the remaining obligations.

Establish `R` using `hA.reads i hi`. Rewrite using `[hkb i hi]`. Use `reads_move' I R (fun β => mvB hI hP A hA i hi β) (fun β => (moveLev (mvEl hI hP A hA i hi β)).U) (fun β => (moveLev (mvEl hI hP A hA i hi β)).chi) (fun β x => Iff.rfl) (fun β x => rfl) (fun β => ?_) (fun β v hv hq hor => ?_) (fun β => ?_)` and prove the remaining obligations. Conclude with `std_move' _ _ (wU i hi β) (mvB_spec hI hP A hA i hi β).1 (R.k_std β)`. Break down `(mvB_spec hI hP A hA i hi β).1 v with e | e` into its components or cases.

Rewrite using `[map_mul, map_inv, e, inv_mul_cancel]`. Rewrite using `[map_mul, map_inv, e, inv_one, one_mul]`. Conclude with `R.k_off β v hv hq hor`. Conclude with `GlobalTheory.TwU.AtTrue.kT_move hPr u (A.kb i β) _ (fun v hv => (mvB_spec hI hP A hA i hi β).2.1 v fun h => h.2.1 hv) (R.k_T β)`. Use `show I.TopPt l Z u a ((mvG hI hP A hA B.R.m β)⁻¹ * A.kb B.R.m β)`.

Rewrite using `[mvG_eq hI hP A hA B.R.m le_rfl β]`. Establish `R` using `hA.reads B.R.m le_rfl`. Take `⟨p₀, hp₀, hN⟩` from `R.k_std β`. Establish `hkl` using `hp₀.lat`. Rewrite `hkl` using `[hN]`.

Establish `hs` using `mvB_spec hI hP A hA B.R.m le_rfl β`. Introduce `d g' g hd he`. Use `isPtOf_move (offPl I u a) (hA.top β d g' g hd he) hp₀.uni hkl (mul_mem (inv_mem (wU _ le_rfl β)) hp₀.uni) (fun v hv => ?_) (fun v hv => ?_) (fun P hP' hv => hv.2.1 (T_mem_of_vT hPr u hP')) (fun P hP' hv => hv.2.2 ⟨P, hP', rfl⟩) (fun w hw _ => isRed_one_of_topPt I hI hP l Z u a _ …` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, hs.2.2.1 rfl v hv, inv_mul_cancel]`. Rewrite using `[map_mul, map_inv, hs.2.1 v hv, inv_one, one_mul]`.

Take `⟨h1, h2, -⟩` from `hA.kA i hi β`. Establish `hW` using `mvW_spec hI hP A hA i hi β`. Use `⟨mul_mem (inv_mem hW.1) h1, ?_, (GlobalTheory.Mem.WeilTwist.exists_isDetRoot _ _).choose_spec⟩` and prove the remaining obligations. Use `show finM _ (rankN (I.rec7 l Z) i hi) ((mvW hI hP A hA i β)⁻¹ * A.kA i β) = ((mvG hI hP A hA i β)⁻¹ * A.kb i β).1`. Rewrite using `[GlobalTheory.AdForm.StabMove.finM_mul, h2, finM_inv_of hW.2, mvG_eq hI hP A hA i hi β]`.

Both sides reduce to the same expression. Take `⟨hb1, hb2⟩` from `hA.base i hi β`. Use `⟨?_, hb2⟩` and prove the remaining obligations. Use `show TC.PtOf ((mvG hI hP A hA i β)⁻¹ * A.kb i β) _`. Rewrite using `[mvG_eq hI hP A hA i hi β]`.

Establish `R` using `hA.reads i hi`. Take `⟨p₀, hp₀, hN⟩` from `R.k_std β`. Establish `hkl` using `hp₀.lat`. Rewrite `hkl` using `[hN]`. Establish `hs` using `mvB_spec hI hP A hA i hi β`.

Distinguish the cases in `hm : i = B.R.m`. Substitute `hm` using the available equality. Establish `hb1' : TC.PtOf (1 * A.kb B.R.m β) (extTo I.SQ (A.p0 B.R.m β).1.1)` using `by rw [one_mul]; exact hb1`. Use `isPtOf_move (offPl I u a) hb1' hp₀.uni hkl (mul_mem (inv_mem (wU _ hi β)) hp₀.uni) (fun v hv => by rw [map_mul, map_inv, hs.2.2.1 rfl v hv, inv_mul_cancel]) (fun v hv => by rw [map_mul, map_inv, hs.2.1 v hv, inv_one, one_mul]) (fun P hP' hv => hv.2.1 (T_mem_of_vT hPr u hP')) (fun …` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis.

Rewrite using `[hs.2.2.2 hm, inv_one, one_mul]`. Conclude with `hb1`. Establish `hW` using `mvW_spec hI hP A hA i hi β`. Use `show (MulAut.conj (mvW hI hP A hA i β)).toMonoidHom g ∈ A.U i β ↔ _`. Rewrite using `[MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hA.U i hi β, GlobalTheory.AdForm.StabMove.finM_mul, GlobalTheory.AdForm.StabMove.finM_mul, hW.2, finM_inv_of hW.2]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hg, κ, hκ⟩`. Use `⟨?_, ⟨(mvEl hI hP A hA i hi β).1⁻¹ * κ.1 * (mvEl hI hP A hA i hi β).1, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e : g = (mvW hI hP A hA i β)⁻¹ * (mvW hI hP A hA i β * g * (mvW hI hP A hA i β)⁻¹) * mvW hI hP A hA i β` using `by group`. Rewrite using `[e]`.

Conclude with `mul_mem (mul_mem (inv_mem hW.1) hg) hW.1`. Use `show (mvEl hI hP A hA i hi β).1 * ((mvEl hI hP A hA i hi β).1⁻¹ * κ.1 * (mvEl hI hP A hA i hi β).1) * (mvEl hI hP A hA i hi β).1⁻¹ ∈ (A.K i hi β).lev.U`. Establish `e : (mvEl hI hP A hA i hi β).1 * ((mvEl hI hP A hA i hi β).1⁻¹ * κ.1 * (mvEl hI hP A hA i hi β).1) * (mvEl hI hP A hA i hi β).1⁻¹ = κ.1` using `by group`. Rewrite using `[e]`. Conclude with `κ.2`.

Use `show ((mvEl hI hP A hA i hi β).1⁻¹ * κ.1 * (mvEl hI hP A hA i hi β).1).1 = _`. Rewrite using `[Units.val_mul, Units.val_mul, hκ]`. Simplify using `[Matrix.mul_assoc]`. Introduce and unpack `⟨hg, κ, hκ⟩`. Use `⟨mul_mem (mul_mem hW.1 hg) (inv_mem hW.1), ⟨(mvEl hI hP A hA i hi β).1 * κ.1 * (mvEl hI hP A hA i hi β).1⁻¹, κ.2⟩, ?_⟩` and prove the remaining obligations.

Use `show ((mvEl hI hP A hA i hi β).1 * κ.1 * (mvEl hI hP A hA i hi β).1⁻¹).1 = _`. Rewrite using `[Units.val_mul, Units.val_mul, hκ]`. Establish `hW` using `mvW_spec hI hP A hA i hi β`. Use `show A.chi i β ⟨mvW hI hP A hA i β * g.1 * (mvW hI hP A hA i β)⁻¹, g.2⟩ = (A.K i hi β).lev.chi ⟨(mvEl hI hP A hA i hi β).1 * κ.1 * (mvEl hI hP A hA i hi β).1⁻¹, κ.2⟩`. Apply `hA.chi i hi β` to reduce the goal to its premises.

Use `show ((mvEl hI hP A hA i hi β).1 * κ.1 * (mvEl hI hP A hA i hi β).1⁻¹).1 = finM _ _ (mvW hI hP A hA i β * g.1 * (mvW hI hP A hA i β)⁻¹)`. Rewrite using `[GlobalTheory.AdForm.StabMove.finM_mul, GlobalTheory.AdForm.StabMove.finM_mul, hW.2, finM_inv_of hW.2, Units.val_mul, Units.val_mul, hκ]`. Establish `hW` using `mvW_spec hI hP A hA i hi β`. Take `⟨h1, h2⟩` from `hA.h i hi β c`. Use `⟨mul_mem h1 hW.1, ?_⟩` and prove the remaining obligations.

Use `show finM _ _ (A.h i β c * mvW hI hP A hA i β) = ((A.K i hi β).y c * basePtU (mvEl hI hP A hA i hi β)).1.1`. Rewrite using `[GlobalTheory.AdForm.StabMove.finM_mul, h2, hW.2]`. Both sides reduce to the same expression. Take `⟨n, hn, h⟩` from `hA.fin i hi β`. Conclude with `⟨n, hn, fun κ => h ⟨(mvEl hI hP A hA i hi β).1 * κ.1 * (mvEl hI hP A hA i hi β).1⁻¹, κ.2⟩⟩`.
-/
theorem moved_is (hI : I.Ok) (hP : TC.Pins B X) (A : TwDat I l Z u a Ch) (hA : A.Is) : (moved hI hP A hA).Is := by
  have hPr := l.pr
  have wU : ∀ i (hi : i ≤ B.R.m) β, mvB hI hP A hA i hi β ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) := by
    intro i hi β
    have hgr : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
    have h : mvB hI hP A hA i hi β ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi)
        (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := ((mem_basePts_iff _ _).1 (mvEl hI hP A hA i hi β).2).1
    have h2 := GlobalTheory.TwU.AtTrue.mem_UPts_one hgr h
    exact h2
  have hkb : ∀ i (hi : i ≤ B.R.m), (moved hI hP A hA).kb i =
      fun β => (mvB hI hP A hA i hi β)⁻¹ * A.kb i β := fun i hi => funext fun β => by
    show (mvG hI hP A hA i β)⁻¹ * A.kb i β = _
    rw [mvG_eq hI hP A hA i hi β]
  refine ⟨fun i hi => ?_, fun β => ?_, fun i hi β => ?_, fun i hi β => ?_, fun i hi c => hA.rep i hi c, fun i hi β g => ?_,
    fun i hi β g κ hκ => ?_, fun i hi β c => ?_, hA.chr, hA.idem, fun i hi β => ?_, hA.bad_le⟩
  ·
    have R := hA.reads i hi
    rw [hkb i hi]
    refine reads_move' I R (fun β => mvB hI hP A hA i hi β) (fun β => (moveLev (mvEl hI hP A hA i hi β)).U)
      (fun β => (moveLev (mvEl hI hP A hA i hi β)).chi) (fun β x => Iff.rfl) (fun β x => rfl) (fun β => ?_) (fun β v hv hq hor => ?_)
      (fun β => ?_)
    · exact std_move' _ _ (wU i hi β) (mvB_spec hI hP A hA i hi β).1 (R.k_std β)
    · rcases (mvB_spec hI hP A hA i hi β).1 v with e | e
      · rw [map_mul, map_inv, e, inv_mul_cancel]
      · rw [map_mul, map_inv, e, inv_one, one_mul]
        exact R.k_off β v hv hq hor
    · exact GlobalTheory.TwU.AtTrue.kT_move hPr u (A.kb i β) _ (fun v hv => (mvB_spec hI hP A hA i hi β).2.1 v fun h => h.2.1 hv)
        (R.k_T β)
  ·
    show I.TopPt l Z u a ((mvG hI hP A hA B.R.m β)⁻¹ * A.kb B.R.m β)
    rw [mvG_eq hI hP A hA B.R.m le_rfl β]
    have R := hA.reads B.R.m le_rfl
    obtain ⟨p₀, hp₀, hN⟩ := R.k_std β
    have hkl := hp₀.lat
    rw [hN] at hkl
    have hs := mvB_spec hI hP A hA B.R.m le_rfl β
    intro d g' g hd he
    refine isPtOf_move (offPl I u a) (hA.top β d g' g hd he) hp₀.uni hkl (mul_mem (inv_mem (wU _ le_rfl β)) hp₀.uni)
      (fun v hv => ?_) (fun v hv => ?_) (fun P hP' hv => hv.2.1 (T_mem_of_vT hPr u hP')) (fun P hP' hv => hv.2.2 ⟨P, hP', rfl⟩)
      (fun w hw _ => isRed_one_of_topPt I hI hP l Z u a _ hkl (hA.top β) w hw)
    · rw [map_mul, map_inv, hs.2.2.1 rfl v hv, inv_mul_cancel]
    · rw [map_mul, map_inv, hs.2.1 v hv, inv_one, one_mul]
  ·
    obtain ⟨h1, h2, -⟩ := hA.kA i hi β
    have hW := mvW_spec hI hP A hA i hi β
    refine ⟨mul_mem (inv_mem hW.1) h1, ?_, (GlobalTheory.Mem.WeilTwist.exists_isDetRoot _ _).choose_spec⟩
    show finM _ (rankN (I.rec7 l Z) i hi) ((mvW hI hP A hA i β)⁻¹ * A.kA i β) = ((mvG hI hP A hA i β)⁻¹ * A.kb i β).1
    rw [GlobalTheory.AdForm.StabMove.finM_mul, h2, finM_inv_of hW.2, mvG_eq hI hP A hA i hi β]
    rfl
  ·
    obtain ⟨hb1, hb2⟩ := hA.base i hi β
    refine ⟨?_, hb2⟩
    show TC.PtOf ((mvG hI hP A hA i β)⁻¹ * A.kb i β) _
    rw [mvG_eq hI hP A hA i hi β]
    have R := hA.reads i hi
    obtain ⟨p₀, hp₀, hN⟩ := R.k_std β
    have hkl := hp₀.lat
    rw [hN] at hkl
    have hs := mvB_spec hI hP A hA i hi β
    by_cases hm : i = B.R.m
    · subst hm
      have hb1' : TC.PtOf (1 * A.kb B.R.m β) (extTo I.SQ (A.p0 B.R.m β).1.1) := by rw [one_mul]; exact hb1
      have := isPtOf_move (offPl I u a) hb1' hp₀.uni hkl (mul_mem (inv_mem (wU _ hi β)) hp₀.uni)
        (fun v hv => by rw [map_mul, map_inv, hs.2.2.1 rfl v hv, inv_mul_cancel])
        (fun v hv => by rw [map_mul, map_inv, hs.2.1 v hv, inv_one, one_mul])
        (fun P hP' hv => hv.2.1 (T_mem_of_vT hPr u hP')) (fun P hP' => not_offPl_SQ hI hP')
        (fun w hw _ => isRed_one_of_topPt I hI hP l Z u a _ hkl (hA.top β) w hw)
      rwa [one_mul] at this
    · rw [hs.2.2.2 hm, inv_one, one_mul]
      exact hb1
  ·
    have hW := mvW_spec hI hP A hA i hi β
    show (MulAut.conj (mvW hI hP A hA i β)).toMonoidHom g ∈ A.U i β ↔ _
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hA.U i hi β, GlobalTheory.AdForm.StabMove.finM_mul,
      GlobalTheory.AdForm.StabMove.finM_mul, hW.2, finM_inv_of hW.2]
    constructor
    · rintro ⟨hg, κ, hκ⟩
      refine ⟨?_, ⟨(mvEl hI hP A hA i hi β).1⁻¹ * κ.1 * (mvEl hI hP A hA i hi β).1, ?_⟩, ?_⟩
      · have e : g = (mvW hI hP A hA i β)⁻¹ * (mvW hI hP A hA i β * g * (mvW hI hP A hA i β)⁻¹) * mvW hI hP A hA i β := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem hW.1) hg) hW.1
      · show (mvEl hI hP A hA i hi β).1 * ((mvEl hI hP A hA i hi β).1⁻¹ * κ.1 * (mvEl hI hP A hA i hi β).1) *
          (mvEl hI hP A hA i hi β).1⁻¹ ∈ (A.K i hi β).lev.U
        have e : (mvEl hI hP A hA i hi β).1 * ((mvEl hI hP A hA i hi β).1⁻¹ * κ.1 * (mvEl hI hP A hA i hi β).1) *
          (mvEl hI hP A hA i hi β).1⁻¹ = κ.1 := by group
        rw [e]
        exact κ.2
      · show ((mvEl hI hP A hA i hi β).1⁻¹ * κ.1 * (mvEl hI hP A hA i hi β).1).1 = _
        rw [Units.val_mul, Units.val_mul, hκ]
        simp [Matrix.mul_assoc]
    · rintro ⟨hg, κ, hκ⟩
      refine ⟨mul_mem (mul_mem hW.1 hg) (inv_mem hW.1), ⟨(mvEl hI hP A hA i hi β).1 * κ.1 * (mvEl hI hP A hA i hi β).1⁻¹, κ.2⟩, ?_⟩
      show ((mvEl hI hP A hA i hi β).1 * κ.1 * (mvEl hI hP A hA i hi β).1⁻¹).1 = _
      rw [Units.val_mul, Units.val_mul, hκ]
  ·
    have hW := mvW_spec hI hP A hA i hi β
    show A.chi i β ⟨mvW hI hP A hA i β * g.1 * (mvW hI hP A hA i β)⁻¹, g.2⟩ =
      (A.K i hi β).lev.chi ⟨(mvEl hI hP A hA i hi β).1 * κ.1 * (mvEl hI hP A hA i hi β).1⁻¹, κ.2⟩
    apply hA.chi i hi β
    show ((mvEl hI hP A hA i hi β).1 * κ.1 * (mvEl hI hP A hA i hi β).1⁻¹).1 =
      finM _ _ (mvW hI hP A hA i β * g.1 * (mvW hI hP A hA i β)⁻¹)
    rw [GlobalTheory.AdForm.StabMove.finM_mul, GlobalTheory.AdForm.StabMove.finM_mul, hW.2, finM_inv_of hW.2, Units.val_mul, Units.val_mul, hκ]
  ·
    have hW := mvW_spec hI hP A hA i hi β
    obtain ⟨h1, h2⟩ := hA.h i hi β c
    refine ⟨mul_mem h1 hW.1, ?_⟩
    show finM _ _ (A.h i β c * mvW hI hP A hA i β) = ((A.K i hi β).y c * basePtU (mvEl hI hP A hA i hi β)).1.1
    rw [GlobalTheory.AdForm.StabMove.finM_mul, h2, hW.2]
    rfl
  ·
    obtain ⟨n, hn, h⟩ := hA.fin i hi β
    exact ⟨n, hn, fun κ => h ⟨(mvEl hI hP A hA i hi β).1 * κ.1 * (mvEl hI hP A hA i hi β).1⁻¹, κ.2⟩⟩

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `B X I hI hP l Z u a Ch A hA _`. Use `⟨moved hI hP A hA, moved_is hI hP A hA, fun i hi β => ?_, fun β v hv hq => ?_⟩` and prove the remaining obligations. Use `show (mvG hI hP A hA i β)⁻¹ * A.kb i β = A.kb i β`. Rewrite using `[mvG_eq hI hP A hA i hi.le β, (mvB_spec hI hP A hA i hi.le β).2.2.2 (Nat.ne_of_lt hi), inv_one, one_mul]`. Use `show bc (prV (E := B.host.E) v) ((mvG hI hP A hA B.R.m β)⁻¹ * A.kb B.R.m β) = 1`.

Rewrite using `[mvG_eq hI hP A hA B.R.m le_rfl β]`. Establish `hs` using `mvB_spec hI hP A hA B.R.m le_rfl β`. Distinguish the cases in `hv' : v ∈ offPl I u a`. Rewrite using `[map_mul, map_inv, hs.2.2.1 rfl v hv', inv_mul_cancel]`. Rewrite using `[map_mul, map_inv, hs.2.1 v hv', inv_one, one_mul]`.

Conclude with `(hA.reads B.R.m le_rfl).k_off β v hv hq (Or.inr fun j hj => hv' ⟨⟨j, hj⟩, hv, hq⟩)`.
-/
theorem exists_twDat_top_trivial : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → Nonempty (Unique (Ch B.R.m)) → ∃ A' : TwDat I l Z u a Ch, A'.Is ∧ (∀ i, i < B.R.m → ∀ β, A'.kb i β = A.kb i β) ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (A'.kb B.R.m β) = 1 := by
  intro B X I hI hP l Z u a Ch A hA _
  refine ⟨moved hI hP A hA, moved_is hI hP A hA, fun i hi β => ?_, fun β v hv hq => ?_⟩
  · show (mvG hI hP A hA i β)⁻¹ * A.kb i β = A.kb i β
    rw [mvG_eq hI hP A hA i hi.le β, (mvB_spec hI hP A hA i hi.le β).2.2.2 (Nat.ne_of_lt hi), inv_one, one_mul]
  · show bc (prV (E := B.host.E) v) ((mvG hI hP A hA B.R.m β)⁻¹ * A.kb B.R.m β) = 1
    rw [mvG_eq hI hP A hA B.R.m le_rfl β]
    have hs := mvB_spec hI hP A hA B.R.m le_rfl β
    by_cases hv' : v ∈ offPl I u a
    · rw [map_mul, map_inv, hs.2.2.1 rfl v hv', inv_mul_cancel]
    · rw [map_mul, map_inv, hs.2.1 v hv', inv_one, one_mul]
      exact (hA.reads B.R.m le_rfl).k_off β v hv hq (Or.inr fun j hj => hv' ⟨⟨j, hj⟩, hv, hq⟩)

end Main

end GlobalTheory.AdForm.TopMove
