import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.RowInj

/- English proof (translation)
Establish `hT : (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) ∈ K.T n` using `Subtype.prop (Subtype.val (Subtype.val z))`. Establish `h0 : ∀ p r, p < a → (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) p r = 0` using `fun p r hp => z.2 p r hp`. Establish `hdv : K.dv a q ((Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) a q) = 0` using `dv_lead K _ (D_zero K (Subtype.val z)) a q h0`. Establish `hB : leadC K a q z ∈ (colH K q).B a`. Establish `hz'` using `hz`.

Rewrite `hz'` using `[leadE_eq]`. Unfold `CrystallineSemistableComparison.Cx.cls at hz'`. Rewrite `hz'` using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `hz'`. Establish `hL` using `leadC_eq K a q z hdv`.

Choose the witnesses or unpack the hypotheses as in `⟨v₁, W₁, hW₁, hD, hv⟩ : ∃ (v₁ : K.X a q) (W₁ : (p q : ℕ) → K.X p q), (∀ p r, p + r + 1 ≠ n → W₁ p r = 0) ∧ K.D W₁ = K.sgl a q v₁ ∧ (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) a q - v₁ ∈ (K.col a).B q := by`. Consider the cases of `a with`. Consider the case `zero`. Use `⟨0, 0, fun _ _ _ => rfl, by simp, ?_⟩` and prove the remaining obligations. Establish `hb : leadC K 0 q z ∈ (⊥ : Submodule R ((colH K q).X 0))` using `hB`.

Rewrite `hb` using `[Submodule.mem_bot, hL]`. Unfold `CrystallineSemistableComparison.Cx.cls at hb`. Rewrite `hb` using `[Submodule.Quotient.mk_eq_zero]`. Simplify using `using hb`. Consider the case `succ a'`.

Establish `hb : leadC K (a' + 1) q z ∈ LinearMap.range ((colH K q).d a')` using `hB`. Take `⟨y, hy⟩` from `LinearMap.mem_range.mp hb`. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective (Submodule.comap ((K.col a').Z q).subtype ((K.col a').B q)) y`. Establish `hw : K.dv a' q (w : K.X a' q) = 0` using `w.2`. Use `⟨K.dh a' q w, K.sgl a' q w, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `p r hpr`. Apply `K.sgl_ne` to reduce the goal to its premises. Distinguish the cases in `hp : p = a'`. Use `right`. Introduce `hr`.

Apply `hpr` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Use `left`. Conclude with `hp`. Rewrite using `[DCx.D_sgl, hw, map_zero, smul_zero, add_zero]`.

Rewrite `hy` using `[hL]`. Unfold `CrystallineSemistableComparison.Cx.cls at hy`. Express the relevant statement in the definitionally equal form `(colMap K a').mapH q (Submodule.Quotient.mk w) = _ at hy`. Unfold `CrystallineSemistableComparison.Cx.Hom.mapH at hy`. Rewrite `hy` using `[Submodule.mapQ_apply, Submodule.Quotient.eq]`.

Establish `h2` using `Submodule.neg_mem _ hy`. Rewrite `h2` using `[neg_sub]`. Conclude with `h2`. Take `⟨W, hW, hW'⟩` from `lower_vert K _ hT haq h0 v₁ W₁ hW₁ hD hv`. Conclude with `lower K z W hW hW'`.
-/
theorem clsZ_mem_of_leadE {R : Type} [CommRing R] (K : DCx.{w} R) (n a q : ℕ) (haq : a + q = n)
    (z : Zf K n a) (hz : leadE K a q z = 0) : clsZ K n a z ∈ Ff K n (a + 1) := by
  have hT : (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) ∈ K.T n :=
    Subtype.prop (Subtype.val (Subtype.val z))
  have h0 : ∀ p r, p < a → (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) p r = 0 :=
    fun p r hp => z.2 p r hp
  have hdv : K.dv a q ((Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) a q) = 0 :=
    dv_lead K _ (D_zero K (Subtype.val z)) a q h0
  have hB : leadC K a q z ∈ (colH K q).B a := by
    have hz' := hz
    rw [leadE_eq] at hz'
    unfold CrystallineSemistableComparison.Cx.cls at hz'
    rw [Submodule.Quotient.mk_eq_zero] at hz'
    exact hz'
  have hL := leadC_eq K a q z hdv
  obtain ⟨v₁, W₁, hW₁, hD, hv⟩ : ∃ (v₁ : K.X a q) (W₁ : (p q : ℕ) → K.X p q),
      (∀ p r, p + r + 1 ≠ n → W₁ p r = 0) ∧ K.D W₁ = K.sgl a q v₁ ∧
      (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) a q - v₁ ∈ (K.col a).B q := by
    cases a with
    | zero =>
      refine ⟨0, 0, fun _ _ _ => rfl, by simp, ?_⟩
      have hb : leadC K 0 q z ∈ (⊥ : Submodule R ((colH K q).X 0)) := hB
      rw [Submodule.mem_bot, hL] at hb
      unfold CrystallineSemistableComparison.Cx.cls at hb
      rw [Submodule.Quotient.mk_eq_zero] at hb
      simpa using hb
    | succ a' =>
      have hb : leadC K (a' + 1) q z ∈ LinearMap.range ((colH K q).d a') := hB
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hb
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective
        (Submodule.comap ((K.col a').Z q).subtype ((K.col a').B q)) y
      have hw : K.dv a' q (w : K.X a' q) = 0 := w.2
      refine ⟨K.dh a' q w, K.sgl a' q w, ?_, ?_, ?_⟩
      · intro p r hpr
        apply K.sgl_ne
        by_cases hp : p = a'
        · right
          intro hr
          apply hpr
          omega
        · left
          exact hp
      · rw [DCx.D_sgl, hw, map_zero, smul_zero, add_zero]
      · rw [hL] at hy
        unfold CrystallineSemistableComparison.Cx.cls at hy
        change (colMap K a').mapH q (Submodule.Quotient.mk w) = _ at hy
        unfold CrystallineSemistableComparison.Cx.Hom.mapH at hy
        rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hy
        have h2 := Submodule.neg_mem _ hy
        rw [neg_sub] at h2
        exact h2
  obtain ⟨W, hW, hW'⟩ := lower_vert K _ hT haq h0 v₁ W₁ hW₁ hD hv
  exact lower K z W hW hW'

/- English proof (translation)
Establish `h0 : leadC K a q z = 0` using `Subsingleton.elim _ _`. Rewrite using `[leadE_eq]`. Unfold `CrystallineSemistableComparison.Cx.cls`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `show leadC K a q z ∈ (colH K q).B a`.

Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`.
-/
theorem leadE_eq_zero_of_subsingleton {R : Type} [CommRing R] (K : DCx.{w} R) (n a q : ℕ)
    (hs : Subsingleton ((K.col a).H q)) (z : Zf K n a) : leadE K a q z = 0 := by
  have h0 : leadC K a q z = 0 := Subsingleton.elim _ _
  rw [leadE_eq]
  unfold CrystallineSemistableComparison.Cx.cls
  rw [Submodule.Quotient.mk_eq_zero]
  show leadC K a q z ∈ (colH K q).B a
  rw [h0]
  exact Submodule.zero_mem _

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `b _ hbk x hx`. Establish `hb' : b = a + j + 1` using `by omega`.

Substitute `hb'` using the available equality. Establish `hs` using `Ff_top_subsingleton K (a + j)`. Establish `hxx` using `Subsingleton.elim (⟨x, hx⟩ : ↥(Ff K (a + j) (a + j + 1))) 0`. Simplify using `using congrArg Subtype.val hxx`. Consider the case `succ k ih`.

Introduce `b hb hbk x hx`. Establish `hx' : x ∈ LinearMap.range (clsZ K (a + j) b)` using `hx`. Take `⟨z, rfl⟩` from `LinearMap.mem_range.mp hx'`. Establish `hq : b + (a + j - b) = a + j` using `by omega`. Establish `hz : leadE K b (a + j - b) z = 0` using `leadE_eq_zero_of_subsingleton K (a + j) b (a + j - b) (hK b _ (by omega)) z`.

Conclude with `ih (b + 1) (by omega) (by omega) _ (clsZ_mem_of_leadE K (a + j) b (a + j - b) hq z hz)`.
-/
theorem Ff_eq_zero {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ)
    (hK : ∀ p q, q < a → Subsingleton ((K.col p).H q)) :
    ∀ k b, j < b → b + k = a + j + 1 → ∀ x ∈ Ff K (a + j) b, x = 0 := by
  intro k
  induction k with
  | zero =>
    intro b _ hbk x hx
    have hb' : b = a + j + 1 := by omega
    subst hb'
    have hs := Ff_top_subsingleton K (a + j)
    have hxx := Subsingleton.elim (⟨x, hx⟩ : ↥(Ff K (a + j) (a + j + 1))) 0
    simpa using congrArg Subtype.val hxx
  | succ k ih =>
    intro b hb hbk x hx
    have hx' : x ∈ LinearMap.range (clsZ K (a + j) b) := hx
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx'
    have hq : b + (a + j - b) = a + j := by omega
    have hz : leadE K b (a + j - b) z = 0 :=
      leadE_eq_zero_of_subsingleton K (a + j) b (a + j - b) (hK b _ (by omega)) z
    exact ih (b + 1) (by omega) (by omega) _ (clsZ_mem_of_leadE K (a + j) b (a + j - b) hq z hz)

/- English proof (translation)
Introduce `R _ K a j hK z hz`. Conclude with `Ff_eq_zero K a j hK a (j + 1) (by omega) (by omega) _ (clsZ_mem_of_leadE K (a + j) j a (by omega) z hz)`.
-/
theorem clsZ_eq_zero_of_leadE : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, leadE K j a z = 0 → clsZ K (a + j) j z = 0 := by
  intro R _ K a j hK z hz
  exact Ff_eq_zero K a j hK a (j + 1) (by omega) (by omega) _
    (clsZ_mem_of_leadE K (a + j) j a (by omega) z hz)

end GlobalTheory.CompanionTheory.RowInj
