import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.Regroup

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `: (ε : 𝓞 F) • a ∈ (I : Submodule (𝓞 F) F)` using `Submodule.smul_mem _ _ ha`. Rewrite `this` using `[Algebra.smul_def]`. Then use the resulting hypothesis.
-/
theorem unit_mul_mem {I : FractionalIdeal (𝓞 F)⁰ F} (ε : (𝓞 F)ˣ) {a : F} (ha : a ∈ I) :
    ((ε : 𝓞 F) : F) * a ∈ I := by
  have : (ε : 𝓞 F) • a ∈ (I : Submodule (𝓞 F) F) := Submodule.smul_mem _ _ ha
  rwa [Algebra.smul_def] at this

/- English proof (translation)
Establish `h1 : ((ε : 𝓞 F) : F) = 1` using `mul_right_cancel₀ hb (h.trans (one_mul b).symm)`. Apply `Units.ext` to reduce the goal to its premises. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `using h1`.
-/
theorem unit_eq_one {ε : (𝓞 F)ˣ} {b : F} (hb : b ≠ 0) (h : ((ε : 𝓞 F) : F) * b = b) : ε = 1 := by
  have h1 : ((ε : 𝓞 F) : F) = 1 := mul_right_cancel₀ hb (h.trans (one_mul b).symm)
  apply Units.ext
  apply RingOfIntegers.ext
  simpa using h1

variable (𝔞 𝔟 : Frac F)

/- English proof (translation)
The claim follows from `Quotient.sound (Exists.intro ε ⟨h1, h2⟩)`.
-/
theorem mk_eq {p q : LatPair 𝔞 𝔟} (ε : (𝓞 F)ˣ) (h1 : q.1.1 = ((ε : 𝓞 F) : F) * p.1.1)
    (h2 : q.1.2 = ((ε : 𝓞 F) : F) * p.1.2) : Quotient.mk (latRel 𝔞 𝔟) p = Quotient.mk _ q :=
  Quotient.sound (Exists.intro ε ⟨h1, h2⟩)

/- English proof (translation)
The claim follows from `Quotient.sound (Exists.intro ε h)`.
-/
theorem mkU_eq {I : FractionalIdeal (𝓞 F)⁰ F} {x y : NZ I} (ε : (𝓞 F)ˣ) (h : y.1 = ((ε : 𝓞 F) : F) * x.1) :
    Quotient.mk (unitRel I) x = Quotient.mk _ y :=
  Quotient.sound (Exists.intro ε h)

def leftPt (c : Quotient (unitRel (latM 𝔞))) : LatPair 𝔞 𝔟 :=
  ⟨(c.out.1, 0), c.out.2.1, ((𝔟 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F).zero_mem, fun h => c.out.2.2 (congrArg Prod.fst h)⟩

def rightPt (c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) (a : {a : F // a ∈ latM 𝔞}) : LatPair 𝔞 𝔟 :=
  ⟨(a.1, c.out.1), a.2, c.out.2.1, fun h => c.out.2.2 (congrArg Prod.snd h)⟩

def regroupMap : Quotient (unitRel (latM 𝔞)) ⊕
    (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)), {a : F // a ∈ latM 𝔞}) → Quotient (latRel 𝔞 𝔟)
  | Sum.inl c => Quotient.mk _ (leftPt 𝔞 𝔟 c)
  | Sum.inr s => Quotient.mk _ (rightPt 𝔞 𝔟 s.1 s.2)

/- English proof (translation)
Introduce and unpack `(c | ⟨c, a⟩) (c' | ⟨c', a'⟩) h`. Take `⟨ε, h1, -⟩` from `Quotient.exact h`. Use `congr 1`. Rewrite using `[← Quotient.out_eq c, ← Quotient.out_eq c']`. Conclude with `mkU_eq ε h1`.

Take `⟨ε, -, h2⟩` from `Quotient.exact h`. Conclude with `absurd (h2.trans (mul_zero _)) c'.out.2.2`. Take `⟨ε, -, h2⟩` from `Quotient.exact h dsimp only [leftPt, rightPt] at h2`. Use `congrArg (fun x => (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * x) h2` as an intermediate fact. Simplify using `only [← mul_assoc, unit_inv_mul, one_mul, mul_zero] at this`.

Conclude with `absurd this.symm c.out.2.2`. Take `⟨ε, h1, h2⟩` from `Quotient.exact h`. Establish `hc : c = c'`. Rewrite using `[← Quotient.out_eq c, ← Quotient.out_eq c']`. Conclude with `mkU_eq ε h2`.

Substitute `hc` using the available equality. Establish `hε : ε = 1` using `unit_eq_one c.out.2.2 h2.symm`. Substitute `hε` using the available equality. Establish `ha : a' = a` using `Subtype.ext (by simpa [rightPt] using h1)`. Substitute `ha` using the available equality.

Both sides reduce to the same expression.
-/
theorem regroupMap_injective : Function.Injective (regroupMap 𝔞 𝔟) := by
  rintro (c | ⟨c, a⟩) (c' | ⟨c', a'⟩) h
  · obtain ⟨ε, h1, -⟩ := Quotient.exact h
    congr 1
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact mkU_eq ε h1
  · obtain ⟨ε, -, h2⟩ := Quotient.exact h
    exact absurd (h2.trans (mul_zero _)) c'.out.2.2
  · obtain ⟨ε, -, h2⟩ := Quotient.exact h
    dsimp only [leftPt, rightPt] at h2
    have := congrArg (fun x => (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * x) h2
    simp only [← mul_assoc, unit_inv_mul, one_mul, mul_zero] at this
    exact absurd this.symm c.out.2.2
  · obtain ⟨ε, h1, h2⟩ := Quotient.exact h
    have hc : c = c' := by
      rw [← Quotient.out_eq c, ← Quotient.out_eq c']
      exact mkU_eq ε h2
    subst hc
    have hε : ε = 1 := unit_eq_one c.out.2.2 h2.symm
    subst hε
    have ha : a' = a := Subtype.ext (by simpa [rightPt] using h1)
    subst ha
    rfl

/- English proof (translation)
Introduce `q`. Proceed by induction on `q using Quotient.inductionOn with`. Consider the case `h p`. Take `⟨⟨a, b⟩, ha, hb, hne⟩` from `p`. Distinguish the cases in `hb0 : b = 0`.

Substitute `hb0` using the available equality. Establish `ha0 : a ≠ 0` using `fun h => hne (by simp [h])`. Take `⟨ε, hε⟩ : (unitRel (latM 𝔞)).r ⟨a, ha, ha0⟩ (Quotient.mk (unitRel (latM 𝔞)) ⟨a, ha, ha0⟩).out` from `Quotient.exact (Quotient.out_eq _).symm`. Conclude with `⟨Sum.inl (Quotient.mk _ ⟨a, ha, ha0⟩), (mk_eq 𝔞 𝔟 ε hε (mul_zero _).symm).symm⟩`. Take `⟨ε, hε⟩ : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r ⟨b, hb, hb0⟩ (Quotient.mk (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ⟨b, hb, hb0⟩).out` from `Quotient.exact (Quotient.out_eq _).symm`.

Conclude with `⟨Sum.inr ⟨Quotient.mk _ ⟨b, hb, hb0⟩, ⟨_, unit_mul_mem ε ha⟩⟩, (mk_eq 𝔞 𝔟 ε rfl hε).symm⟩`.
-/
theorem regroupMap_surjective : Function.Surjective (regroupMap 𝔞 𝔟) := by
  intro q
  induction q using Quotient.inductionOn with
  | h p =>
  obtain ⟨⟨a, b⟩, ha, hb, hne⟩ := p
  by_cases hb0 : b = 0
  · subst hb0
    have ha0 : a ≠ 0 := fun h => hne (by simp [h])
    obtain ⟨ε, hε⟩ : (unitRel (latM 𝔞)).r ⟨a, ha, ha0⟩ (Quotient.mk (unitRel (latM 𝔞)) ⟨a, ha, ha0⟩).out :=
      Quotient.exact (Quotient.out_eq _).symm
    exact ⟨Sum.inl (Quotient.mk _ ⟨a, ha, ha0⟩), (mk_eq 𝔞 𝔟 ε hε (mul_zero _).symm).symm⟩
  · obtain ⟨ε, hε⟩ : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r ⟨b, hb, hb0⟩
        (Quotient.mk (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ⟨b, hb, hb0⟩).out :=
      Quotient.exact (Quotient.out_eq _).symm
    exact ⟨Sum.inr ⟨Quotient.mk _ ⟨b, hb, hb0⟩, ⟨_, unit_mul_mem ε ha⟩⟩, (mk_eq 𝔞 𝔟 ε rfl hε).symm⟩

/- English proof (translation)
Take `⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r (Quotient.mk (latRel 𝔞 𝔟) p).out p` from `Quotient.exact (Quotient.out_eq _)`. Establish `: p.1 = (((ε : 𝓞 F) : F) * (Quotient.mk (latRel 𝔞 𝔟) p).out.1.1, ((ε : 𝓞 F) : F) * (Quotient.mk (latRel 𝔞 𝔟) p).out.1.2)` using `Prod.ext h1 h2`. Rewrite using `[this, hg]`.
-/
theorem g_out {g : F × F → ℂ}
    (hg : ∀ (ε : (𝓞 F)ˣ) (a b : F), g (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) = g (a, b))
    (p : LatPair 𝔞 𝔟) : g (Quotient.mk (latRel 𝔞 𝔟) p).out.1 = g p.1 := by
  obtain ⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r (Quotient.mk (latRel 𝔞 𝔟) p).out p := Quotient.exact (Quotient.out_eq _)
  have : p.1 = (((ε : 𝓞 F) : F) * (Quotient.mk (latRel 𝔞 𝔟) p).out.1.1,
      ((ε : 𝓞 F) : F) * (Quotient.mk (latRel 𝔞 𝔟) p).out.1.2) := Prod.ext h1 h2
  rw [this, hg]

end GlobalTheory.HeckeTwo.Regroup

/- English proof (translation)
Introduce `F _ _ 𝔞 𝔟 g hg hs`. Use `open GlobalTheory.HeckeTwo.Regroup in`. Set `e` to `Equiv.ofBijective _ ⟨regroupMap_injective 𝔞 𝔟, regroupMap_surjective 𝔞 𝔟⟩`. Set `h : Quotient (unitRel (latM 𝔞)) ⊕ (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), {a : F // a ∈ latM 𝔞}) → ℂ` to `Sum.elim (fun c => g (c.out.1, 0)) (fun s => g (s.2.1, s.1.out.1))`. Establish `hfe : (fun c : Quotient (latRel 𝔞 𝔟) => g c.out.1) ∘ e = h`.

Use function extensionality and compare the values at `x`. Break down `x with c | ⟨c, a⟩` into its components or cases. Conclude with `GlobalTheory.HeckeTwo.Regroup.g_out 𝔞 𝔟 hg _`. Conclude with `GlobalTheory.HeckeTwo.Regroup.g_out 𝔞 𝔟 hg _`. Establish `hsh : Summable h` using `hfe ▸ (e.summable_iff).2 hs`.

Establish `hl : Summable (h ∘ Sum.inl)` using `hsh.comp_injective Sum.inl_injective`. Establish `hr : Summable (h ∘ Sum.inr)` using `hsh.comp_injective Sum.inr_injective`. Establish `hr' : Summable (fun s : (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), {a : F // a ∈ latM 𝔞}) => g (s.2.1, s.1.out.1))` using `hr`. Use `⟨hl, fun c => hr'.sigma_factor c, hr'.sigma, ?_⟩` and prove the remaining obligations. Rewrite using `[← e.tsum_eq, show (∑' x, g (e x).out.1) = ∑' x, h x from congrArg tsum hfe, hl.tsum_sum hr]`.

Conclude with `congrArg₂ (· + ·) rfl hr'.tsum_sigma`.
-/
theorem GlobalTheory.HeckeTwo.Regroup.tsum_latRel_regroup : ∀ (F : Type) [Field F] [NumberField F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (g : F × F → ℂ), (∀ (ε : (NumberField.RingOfIntegers F)ˣ) (a b : F), g (((ε : NumberField.RingOfIntegers F) : F) * a, ((ε : NumberField.RingOfIntegers F) : F) * b) = g (a, b)) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => g c.out.1) → Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)) => g (c.out.1, 0)) ∧ (∀ c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => g (a.1, c.out.1))) ∧ Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1)) ∧ ∑' c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟), g c.out.1 = ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)), g (c.out.1, 0) + ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1) := by
  intro F _ _ 𝔞 𝔟 g hg hs
  open GlobalTheory.HeckeTwo.Regroup in
  let e := Equiv.ofBijective _ ⟨regroupMap_injective 𝔞 𝔟, regroupMap_surjective 𝔞 𝔟⟩
  let h : Quotient (unitRel (latM 𝔞)) ⊕
      (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), {a : F // a ∈ latM 𝔞}) → ℂ :=
    Sum.elim (fun c => g (c.out.1, 0)) (fun s => g (s.2.1, s.1.out.1))
  have hfe : (fun c : Quotient (latRel 𝔞 𝔟) => g c.out.1) ∘ e = h := by
    funext x
    rcases x with c | ⟨c, a⟩
    · exact GlobalTheory.HeckeTwo.Regroup.g_out 𝔞 𝔟 hg _
    · exact GlobalTheory.HeckeTwo.Regroup.g_out 𝔞 𝔟 hg _
  have hsh : Summable h := hfe ▸ (e.summable_iff).2 hs
  have hl : Summable (h ∘ Sum.inl) := hsh.comp_injective Sum.inl_injective
  have hr : Summable (h ∘ Sum.inr) := hsh.comp_injective Sum.inr_injective
  have hr' : Summable (fun s : (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)),
      {a : F // a ∈ latM 𝔞}) => g (s.2.1, s.1.out.1)) := hr
  refine ⟨hl, fun c => hr'.sigma_factor c, hr'.sigma, ?_⟩
  rw [← e.tsum_eq, show (∑' x, g (e x).out.1) = ∑' x, h x from congrArg tsum hfe, hl.tsum_sum hr]
  exact congrArg₂ (· + ·) rfl hr'.tsum_sigma
