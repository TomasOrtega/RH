import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimes

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.ChiStd

variable {D : D7}

/- English proof (translation)
Take `⟨α, rfl, -, h0⟩` from `hε`. Establish `h0' : (Formalism.UG.evalV D.host.F v') ((sndA D.host.F) (pairA D.host.F 0 α)) = 0` using `h0 v' hv`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => rw [mul_zero, RingHom.map_zero, RingHom.map_zero]`. Consider the case `tmul x y`.

Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]`. Simplify using `[Formalism.IndefR.Datum.toEAf, finPart, Formalism.UG.prV]`. Rewrite using `[h0', zero_mul, TensorProduct.tmul_zero]`. Consider the case `add x y hx hy => rw [mul_add, RingHom.map_add, RingHom.map_add, hx, hy, add_zero]`.
-/
theorem prV_toEAf_idem_mul {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (hv : v' ≠ v) (a : AE D) :
    Formalism.UG.prV (E := D.host.E) v' (Formalism.IndefR.Datum.toEAf D (algebraMap (AF D.host.F) (AE D) ε * a)) = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  have h0' : (Formalism.UG.evalV D.host.F v') ((sndA D.host.F) (pairA D.host.F 0 α)) = 0 := h0 v' hv
  induction a using TensorProduct.induction_on with
  | zero => rw [mul_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    simp [Formalism.IndefR.Datum.toEAf, finPart, Formalism.UG.prV]
    rw [h0', zero_mul, TensorProduct.tmul_zero]
  | add x y hx hy => rw [mul_add, RingHom.map_add, RingHom.map_add, hx, hy, add_zero]

end GlobalTheory.AdForm.ChiStd

namespace GlobalTheory.AdForm.ChiStd

variable {D : D7}

/- English proof (translation)
Take `⟨ε, hε, he⟩` from `p.above`. Establish `hs` using `β.gl_supp g`. Substitute `hn` using the available equality. Use extensionality with `r s`. Establish `key : Formalism.UG.prV (E` using `D.host.E) v' (Formalism.IndefR.Datum.toEAf D ((mt S (β.gl g) - 1) r s)) = 0 := by`.

Rewrite using `[← hs r s, he]`. Conclude with `prV_toEAf_idem_mul hε hv _`. Establish `e1 : mt S (β.gl g) r s = (mt S (β.gl g) - 1) r s + (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) r s`. Rewrite using `[Matrix.sub_apply, sub_add_cancel]`. Simplify using `only [finM, Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_refl, Equiv.refl_symm, Equiv.refl_apply]`.

Rewrite using `[e1, RingHom.map_add, RingHom.map_add, key, zero_add, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem finM_gl_map_prV {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) {n : ℕ} (hn : S.rank = n) {m : Type} [Fintype m] [DecidableEq m] (β : Frame p S m)
    (g : GL m k) {v' : HeightOneSpectrum (𝓞 D.host.F)} (hv : v' ≠ p.v) :
    (finM S hn (β.gl g)).map (Formalism.UG.prV (E := D.host.E) v') = 1 := by
  obtain ⟨ε, hε, he⟩ := p.above
  have hs := β.gl_supp g
  subst hn
  ext r s
  have key : Formalism.UG.prV (E := D.host.E) v' (Formalism.IndefR.Datum.toEAf D ((mt S (β.gl g) - 1) r s)) = 0 := by
    rw [← hs r s, he]; exact prV_toEAf_idem_mul hε hv _
  have e1 : mt S (β.gl g) r s = (mt S (β.gl g) - 1) r s + (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) r s := by
    rw [Matrix.sub_apply, sub_add_cancel]
  simp only [finM, Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_refl, Equiv.refl_symm,
    Equiv.refl_apply]
  rw [e1, RingHom.map_add, RingHom.map_add, key, zero_add, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp
end GlobalTheory.AdForm.ChiStd

/- English proof (translation)
Establish `hcop : Nat.Coprime a c` using `(Nat.coprime_primes ha hc).2 hne`. Establish `hg : ((Nat.gcd a c : ℕ) : ℤ) = a * Nat.gcdA a c + c * Nat.gcdB a c` using `Nat.gcd_eq_gcd_ab a c`. Rewrite `hg` using `[hcop, Nat.cast_one]`. Establish `h3 : ((1 : ℤ) : 𝓞 F) ∈ v.asIdeal`. Rewrite using `[hg]`.

Use `push_cast`. Conclude with `v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ h1) (v.asIdeal.mul_mem_right _ h2)`. Rewrite `h3` using `[Int.cast_one]`. Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)`.
-/
theorem GlobalTheory.AdForm.ChiStd.not_both_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a c : ℕ}
    (ha : a.Prime) (hc : c.Prime) (hne : a ≠ c) (h1 : ((a : ℕ) : 𝓞 F) ∈ v.asIdeal) (h2 : ((c : ℕ) : 𝓞 F) ∈ v.asIdeal) : False := by
  have hcop : Nat.Coprime a c := (Nat.coprime_primes ha hc).2 hne
  have hg : ((Nat.gcd a c : ℕ) : ℤ) = a * Nat.gcdA a c + c * Nat.gcdB a c := Nat.gcd_eq_gcd_ab a c
  rw [hcop, Nat.cast_one] at hg
  have h3 : ((1 : ℤ) : 𝓞 F) ∈ v.asIdeal := by
    rw [hg]; push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ h1) (v.asIdeal.mul_mem_right _ h2)
  rw [Int.cast_one] at h3
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS j hj b i g hg h`. Take `⟨κ, hκ⟩` from `((hA.U j hj b _).1 h).2`. Rewrite using `[hA.chi j hj b ⟨_, h⟩ κ hκ]`. Apply `hA.lev_chi_eq_one j hj b κ` to reduce the goal to its premises. Introduce `v' hv'`.

Establish `hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∈ (p i).v.asIdeal`. Take `⟨⟨e, he⟩, -⟩` from `hS`. Take `⟨-, hPr, -⟩` from `GlobalTheory.Mem.Col2.base_fields_primes_ok B X`. Establish `hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u))` using `hPr.piT_cop u`. Establish `hne : X.piT u ≠ 0`.

Introduce `h0`. Rewrite `hcop` using `[h0, map_zero, isCoprime_zero_left]`. Conclude with `not_isUnit_zero hcop`. Establish `hmem : X.piT u ∈ (e i).1.asIdeal` using `(Formalism.L2.Col.mem_divs hne _).1 (e i).2`. Take `⟨ε, hε, hε'⟩` from `(p i).above`.

Establish `hund` using `GlobalTheory.IdemUnder.under_eq_of_isIdemAt (I.rec7 l Z) (p i).e (e i).1 (p i).v ε (he i) hε hε'`. Establish `hTE : ((B.T u : ℕ) : 𝓞 B.host.E) ∈ (e i).1.asIdeal`. Use `hPr.piT_norm u` as an intermediate fact. Rewrite using `[← this]`. Conclude with `Ideal.mul_mem_right _ _ hmem`.

Rewrite using `[← hund]`. Use `show _ ∈ Ideal.comap _ _`. Use `Ideal.mem_comap.2 ?_` and prove the remaining obligations. Establish `h2 : (algebraMap (𝓞 (I.rec7 l Z).host.F) (𝓞 (I.rec7 l Z).host.E)) ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) = ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.E)` using `map_natCast _ _`. Apply the tactic sequence `first | (erw [h2]; exact hTE) | exact h2 ▸ hTE | simpa using hTE`.

Establish `hne : v' ≠ (p i).v`. Introduce and unpack `rfl`. Take `⟨-, hPr, -⟩` from `GlobalTheory.Mem.Col2.base_fields_primes_ok B X`. Break down `hv' with hbad | hq` into its components or cases. Break down `hbad with h0 | h1` into its components or cases.

Conclude with `GlobalTheory.AdForm.ChiStd.not_both_mem _ (hPr.T_prime u) (hPr.g_prime 0) (hPr.T_ne_g u 0) hT h0`. Conclude with `GlobalTheory.AdForm.ChiStd.not_both_mem _ (hPr.T_prime u) (hPr.g_prime 1) (hPr.T_ne_g u 1) hT h1`. Conclude with `(GlobalTheory.Mem.Col2.TC.underQ_notMem I hOk l u a _ hq).1 hT`. Apply `Units.ext` to reduce the goal to its premises. Use `show (κ.1.1).map (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v') = 1`.

Rewrite using `[hκ]`. Conclude with `GlobalTheory.AdForm.ChiStd.finM_gl_map_prV (p i) _ _ (β j i) g hne`.
-/
theorem GlobalTheory.AdForm.chi_std_trivial : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i → ∀ h : (β j i).gl g ∈ A.U j b, A.chi j b ⟨_, h⟩ = 1 := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS j hj b i g hg h
  obtain ⟨κ, hκ⟩ := ((hA.U j hj b _).1 h).2
  rw [hA.chi j hj b ⟨_, h⟩ κ hκ]
  apply hA.lev_chi_eq_one j hj b κ
  intro v' hv'
  have hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∈ (p i).v.asIdeal := by
    obtain ⟨⟨e, he⟩, -⟩ := hS
    obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
    have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
    have hne : X.piT u ≠ 0 := by
      intro h0
      rw [h0, map_zero, isCoprime_zero_left] at hcop
      exact not_isUnit_zero hcop
    have hmem : X.piT u ∈ (e i).1.asIdeal := (Formalism.L2.Col.mem_divs hne _).1 (e i).2
    obtain ⟨ε, hε, hε'⟩ := (p i).above
    have hund := GlobalTheory.IdemUnder.under_eq_of_isIdemAt (I.rec7 l Z) (p i).e (e i).1 (p i).v ε (he i) hε hε'
    have hTE : ((B.T u : ℕ) : 𝓞 B.host.E) ∈ (e i).1.asIdeal := by
      have := hPr.piT_norm u
      rw [← this]
      exact Ideal.mul_mem_right _ _ hmem
    rw [← hund]
    show _ ∈ Ideal.comap _ _
    refine Ideal.mem_comap.2 ?_
    have h2 : (algebraMap (𝓞 (I.rec7 l Z).host.F) (𝓞 (I.rec7 l Z).host.E)) ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) =
        ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.E) := map_natCast _ _
    first | (erw [h2]; exact hTE) | exact h2 ▸ hTE | simpa using hTE
  have hne : v' ≠ (p i).v := by
    rintro rfl
    obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
    rcases hv' with hbad | hq
    · rcases hbad with h0 | h1
      · exact GlobalTheory.AdForm.ChiStd.not_both_mem _ (hPr.T_prime u) (hPr.g_prime 0) (hPr.T_ne_g u 0) hT h0
      · exact GlobalTheory.AdForm.ChiStd.not_both_mem _ (hPr.T_prime u) (hPr.g_prime 1) (hPr.T_ne_g u 1) hT h1
    · exact (GlobalTheory.Mem.Col2.TC.underQ_notMem I hOk l u a _ hq).1 hT
  apply Units.ext
  show (κ.1.1).map (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v') = 1
  rw [hκ]
  exact GlobalTheory.AdForm.ChiStd.finM_gl_map_prV (p i) _ _ (β j i) g hne
