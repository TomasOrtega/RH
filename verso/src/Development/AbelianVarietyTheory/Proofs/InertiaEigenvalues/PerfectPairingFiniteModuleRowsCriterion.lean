import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.OrthogonalFreeOfPerfectAltZmod

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun
  GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.CharDual

/- English proof (translation)
Use `haveI : NeZero n := ⟨hn⟩`. Use `letI : Module (ZMod n) G := AddCommGroup.zmodModule hG`. Take `⟨f, hf⟩` from `GlobalTheory.ZModPerp.exists_dual_ne_zero (n := n) hg`. Conclude with `⟨f.toAddMonoidHom, hf⟩`.
-/
theorem exists_char_ne_zero (n : ℕ) (hn : n ≠ 0) {G : Type} [AddCommGroup G]
    (hG : ∀ g : G, n • g = 0) {g : G} (hg : g ≠ 0) : ∃ φ : G →+ ZMod n, φ g ≠ 0 := by
  haveI : NeZero n := ⟨hn⟩
  letI : Module (ZMod n) G := AddCommGroup.zmodModule hG
  obtain ⟨f, hf⟩ := GlobalTheory.ZModPerp.exists_dual_ne_zero (n := n) hg
  exact ⟨f.toAddMonoidHom, hf⟩

variable (A : Type) [CommRing A] (n : ℕ)

def charModule : Module A (A →+ ZMod n) where
  smul a φ := φ.comp (AddMonoidHom.mulLeft a)
  one_smul φ := by
    ext b
    show φ (1 * b) = φ b
    rw [one_mul]
  mul_smul a a' φ := by
    ext b
    show φ (a * a' * b) = φ (a' * (a * b))
    rw [mul_left_comm, mul_assoc]
  smul_zero a := by ext b; rfl
  smul_add a φ ψ := by ext b; rfl
  add_smul a a' φ := by
    ext b
    show φ ((a + a') * b) = φ (a * b) + φ (a' * b)
    rw [add_mul, map_add]
  zero_smul φ := by
    ext b
    show φ (0 * b) = 0
    rw [zero_mul, map_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem charModule_smul_apply (a : A) (φ : A →+ ZMod n) (b : A) :
    (@HSMul.hSMul A (A →+ ZMod n) (A →+ ZMod n)
      (@instHSMul A (A →+ ZMod n) (charModule A n).toSMul) a φ) b = φ (a * b) := rfl

end GlobalTheory.NewPrime.CharDual

namespace GlobalTheory.NewPrime

open GlobalTheory.NewPrime.CharDual in

/- English proof (translation)
Introduce `A _ _ n hn hnA`. Use `haveI : NeZero n := ⟨hn⟩`. Use `letI : Module A (A →+ ZMod n) := charModule A n`. Use `haveI : Finite (A →+ ZMod n) := Finite.of_injective (fun φ : A →+ ZMod n => (φ : A → ZMod n)) DFunLike.coe_injective`. Use `⟨A →+ ZMod n, inferInstance, inferInstance, inferInstance, AddMonoidHom.id _, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `a y y'`. Both sides reduce to the same expression. Introduce `y hy`. Use extensionality with `b`. Conclude with `hy b`.

Introduce `y' hy'`. Assume the negation of the conclusion as `h`. Take `⟨φ, hφ⟩` from `exists_char_ne_zero n hn (G := A) (fun g => by`. Rewrite using `[nsmul_eq_mul, hnA, zero_mul]) h`. Conclude with `hφ (hy' φ)`.

Introduce `a Φ v hv`. Assume the negation of the conclusion as `hvr`. Use `set Q := (Fin a → A) ⧸ what₂ Φ`. Establish `hQ : ∀ q : Q, n • q = 0`. Introduce `q`.

Proceed by induction on `q using Submodule.Quotient.induction_on with`. Consider the case `H w => show n • (Submodule.Quotient.mk w : Q) = 0`. Rewrite using `[← Nat.cast_smul_eq_nsmul A, ← Submodule.Quotient.mk_smul, hnA, zero_smul, Submodule.Quotient.mk_zero]`. Establish `hmk : (Submodule.Quotient.mk v : Q) ≠ 0`. Rewrite using `[Ne, Submodule.Quotient.mk_eq_zero]` and apply the resulting hypothesis.

Take `⟨ψ, hψ⟩` from `exists_char_ne_zero n hn hQ hmk`. Set `L : (Fin a → A) →+ ZMod n` to `ψ.comp (what₂ Φ).mkQ.toAddMonoidHom`. Set `x : Fin a → (A →+ ZMod n)` to `fun j => L.comp (AddMonoidHom.single (fun _ => A) j)`. Establish `key : ∀ (w : Fin a → A) (b : A), (∑ j, w j • x j) b = L (fun k => w k * b)`. Introduce `w b`.

Rewrite using `[AddMonoidHom.finset_sum_apply]`. Establish `: (fun k => w k * b) = ∑ j, Pi.single j (w j * b)` using `(Finset.univ_sum_single _).symm`. Rewrite using `[this, map_sum]`. Both sides reduce to the same expression. Establish `hx : matAct Φ x = 0`.

Use function extensionality and compare the values at `i`. Use extensionality with `b`. Use `show (∑ j, Φ i j • x j) b = 0`. Rewrite using `[key]`. Establish `: (fun k => Φ i k * b) = b • Φ i`.

Use function extensionality and compare the values at `k`. Simplify using `[mul_comm]`. Rewrite using `[this]`. Establish `hmem : b • Φ i ∈ what₂ Φ` using `Submodule.smul_mem _ b (Submodule.subset_span ⟨i, rfl⟩)`. Use `show ψ (Submodule.Quotient.mk _) = 0`.

Rewrite using `[(Submodule.Quotient.mk_eq_zero _).2 hmem, map_zero]`. Establish `h1` using `congrArg (fun f : A →+ ZMod n => f 1) (hv x hx)`. Rewrite `h1` using `[key]`. Simplify using `only [mul_one] at h1`. Conclude with `hψ h1`.
-/
theorem charDual_cogenerator : ∀ (A : Type) [CommRing A] [Finite A] (n : ℕ), n ≠ 0 → (n : A) = 0 →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module A Y) (_ : Finite Y) (β : Y →+ A →+ ZMod n),
      Perf A β ∧ ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (v : Fin a → A),
        (∀ x : Fin a → Y, matAct Φ x = 0 → ∑ j, v j • x j = 0) → v ∈ what₂ Φ := by
  intro A _ _ n hn hnA
  haveI : NeZero n := ⟨hn⟩
  letI : Module A (A →+ ZMod n) := charModule A n
  haveI : Finite (A →+ ZMod n) :=
    Finite.of_injective (fun φ : A →+ ZMod n => (φ : A → ZMod n)) DFunLike.coe_injective
  refine ⟨A →+ ZMod n, inferInstance, inferInstance, inferInstance, AddMonoidHom.id _, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a y y'
    rfl
  · intro y hy
    ext b
    exact hy b
  · intro y' hy'
    by_contra h
    obtain ⟨φ, hφ⟩ := exists_char_ne_zero n hn (G := A) (fun g => by
      rw [nsmul_eq_mul, hnA, zero_mul]) h
    exact hφ (hy' φ)
  · intro a Φ v hv
    by_contra hvr
    set Q := (Fin a → A) ⧸ what₂ Φ
    have hQ : ∀ q : Q, n • q = 0 := by
      intro q
      induction q using Submodule.Quotient.induction_on with
      | H w =>
        show n • (Submodule.Quotient.mk w : Q) = 0
        rw [← Nat.cast_smul_eq_nsmul A, ← Submodule.Quotient.mk_smul, hnA, zero_smul,
          Submodule.Quotient.mk_zero]
    have hmk : (Submodule.Quotient.mk v : Q) ≠ 0 := by
      rwa [Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨ψ, hψ⟩ := exists_char_ne_zero n hn hQ hmk
    let L : (Fin a → A) →+ ZMod n := ψ.comp (what₂ Φ).mkQ.toAddMonoidHom
    let x : Fin a → (A →+ ZMod n) := fun j => L.comp (AddMonoidHom.single (fun _ => A) j)
    have key : ∀ (w : Fin a → A) (b : A), (∑ j, w j • x j) b = L (fun k => w k * b) := by
      intro w b
      rw [AddMonoidHom.finset_sum_apply]
      have : (fun k => w k * b) = ∑ j, Pi.single j (w j * b) := (Finset.univ_sum_single _).symm
      rw [this, map_sum]
      rfl
    have hx : matAct Φ x = 0 := by
      funext i
      ext b
      show (∑ j, Φ i j • x j) b = 0
      rw [key]
      have : (fun k => Φ i k * b) = b • Φ i := by
        funext k
        simp [mul_comm]
      rw [this]
      have hmem : b • Φ i ∈ what₂ Φ := Submodule.smul_mem _ b (Submodule.subset_span ⟨i, rfl⟩)
      show ψ (Submodule.Quotient.mk _) = 0
      rw [(Submodule.Quotient.mk_eq_zero _).2 hmem, map_zero]
    have h1 := congrArg (fun f : A →+ ZMod n => f 1) (hv x hx)
    rw [key] at h1
    simp only [mul_one] at h1
    exact hψ h1

end GlobalTheory.NewPrime
