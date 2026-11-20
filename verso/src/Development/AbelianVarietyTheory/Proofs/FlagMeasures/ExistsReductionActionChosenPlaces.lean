import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemKsetActsAsGLModSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialModChosenPrimesIffMemKgStatement

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

/- English proof (translation)
Assume the negation of the conclusion as `hkk`. Establish `hg : g k ≠ g k'`. Introduce `e`. Apply `hkk` to reduce the goal to its premises. Apply the tactic sequence `fin_cases k <;> fin_cases k'`.

Both sides reduce to the same expression. Conclude with `absurd e h.2.1`. Conclude with `absurd e.symm h.2.1`. Both sides reduce to the same expression. Take `⟨a, b, hab⟩ : IsCoprime (g k : ℤ) (g k')` from `Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (h.1 k) (h.1 k')).mpr hg)`.

Establish `e : (a : 𝓞 I.E) * ((g k : ℕ) : 𝓞 I.E) + (b : 𝓞 I.E) * ((g k' : ℕ) : 𝓞 I.E) = 1`. Use `congrArg (Int.cast : ℤ → 𝓞 I.E) hab` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Apply `u.isPrime.ne_top` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one, ← e]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)`.
-/
theorem IsChoice.eq_of_mem {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (h : IsChoice I g Pl w) {k k' : Fin 2}
    (u : HeightOneSpectrum (𝓞 I.E)) (h1 : ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal) (h2 : ((g k' : ℕ) : 𝓞 I.E) ∈ u.asIdeal) :
    k = k' := by
  by_contra hkk
  have hg : g k ≠ g k' := by
    intro e
    apply hkk
    fin_cases k <;> fin_cases k'
    · rfl
    · exact absurd e h.2.1
    · exact absurd e.symm h.2.1
    · rfl
  obtain ⟨a, b, hab⟩ : IsCoprime (g k : ℤ) (g k') :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (h.1 k) (h.1 k')).mpr hg)
  have e : (a : 𝓞 I.E) * ((g k : ℕ) : 𝓞 I.E) + (b : 𝓞 I.E) * ((g k' : ℕ) : 𝓞 I.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 I.E) hab
    push_cast at this
    exact this
  apply u.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

/- English proof (translation)
Take `⟨ka, va⟩` from `a`. Take `⟨kb, vb⟩` from `b`. Simplify using `only`. Establish `hmem` using `h.2.2.2.1`. Distinguish the cases in `hk : kb = ka`.

Substitute `hk` using the available equality. Establish `hv : vb ≠ va` using `fun e => hab (by rw [e])`. Conclude with `⟨fun e => hv (h.2.2.2.2.1 kb e), h.2.2.2.2.2.1 kb va vb⟩`. Use `⟨fun e => hk (h.eq_of_mem (w kb vb) (hmem kb vb).1 (by rw [e]; exact (hmem ka va).1)), fun hcj => hk ?_⟩` and prove the remaining obligations. Establish `hx` using `(hcj ((g ka : ℕ) : 𝓞 I.E) ((g ka : ℕ) : 𝓞 I.E) (by simp)).mp (hmem ka va).1`.

Conclude with `(h.eq_of_mem (w kb vb) hx (hmem kb vb).1).symm`.
-/
theorem IsChoice.ne_of_ne {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (h : IsChoice I g Pl w) {a b : Σ k, Pl k} (hab : b ≠ a) :
    w b.1 b.2 ≠ w a.1 a.2 ∧ ¬ IsConj I (w a.1 a.2) (w b.1 b.2) := by
  obtain ⟨ka, va⟩ := a
  obtain ⟨kb, vb⟩ := b
  dsimp only
  have hmem := h.2.2.2.1
  by_cases hk : kb = ka
  · subst hk
    have hv : vb ≠ va := fun e => hab (by rw [e])
    exact ⟨fun e => hv (h.2.2.2.2.1 kb e), h.2.2.2.2.2.1 kb va vb⟩
  · refine ⟨fun e => hk (h.eq_of_mem (w kb vb) (hmem kb vb).1 (by rw [e]; exact (hmem ka va).1)), fun hcj => hk ?_⟩
    have hx := (hcj ((g ka : ℕ) : 𝓞 I.E) ((g ka : ℕ) : 𝓞 I.E) (by simp)).mp (hmem ka va).1
    exact (h.eq_of_mem (w kb vb) hx (hmem kb vb).1).symm

/- English proof (translation)
Introduce `y h`. Rewrite using `[Matrix.one_mulVec, ← sub_eq_zero, ← map_sub]`. Use `(fr.c_ker _).mpr ?_` and prove the remaining obligations. Establish `e : ((⟨_, h⟩ - y : I.Lf) : Fin I.n → _) = (I.fmat x - 1) *ᵥ (y : Fin I.n → _)`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, Submodule.coe_sub]`.

Rewrite using `[e]`. Conclude with `hx _ y.2`.
-/
theorem PlFrame.actsAs_one_of_mem {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
    {x : I.Gf} (hx : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I w.asIdeal • I.Lf) : fr.ActsAs x 1 := by
  intro y h
  rw [Matrix.one_mulVec, ← sub_eq_zero, ← map_sub]
  refine (fr.c_ker _).mpr ?_
  have e : ((⟨_, h⟩ - y : I.Lf) : Fin I.n → _) = (I.fmat x - 1) *ᵥ (y : Fin I.n → _) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Submodule.coe_sub]
  rw [e]
  exact hx _ y.2

/- English proof (translation)
The claim follows from `Units.ext (PlFrame.ActsAs.unique (fr kv.1 kv.2) hx (hρ x hx kv.1 kv.2) hM)`.
-/
private theorem val_eq_lemma {I : AutInst} {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} {fr : ∀ k v, PlFrame I N (g k) (w k v)}
    {ρ : I.Gf → GProd N g Pl} (hρ : ActsBy fr ρ) {x : I.Gf} (hx : x ∈ I.Kset) (kv : Σ k, Pl k)
    {M : GL (Fin N) (ZMod (g kv.1))} (hM : (fr kv.1 kv.2).ActsAs x (M : Matrix (Fin N) (Fin N) (ZMod (g kv.1)))) :
    ρ x kv = M :=
  Units.ext (PlFrame.ActsAs.unique (fr kv.1 kv.2) hx (hρ x hx kv.1 kv.2) hM)

/- English proof (translation)
Introduce `I N g Pl w fr _ hn hc`. Take `⟨ρ, hρ, hmul⟩` from `exists_actsBy fr`. Establish `hK1 : (1 : I.Gf) ∈ I.Kset` using `(Inhab.mem_Ksub I 1).mp (Inhab.Ksub I).one_mem`. Establish `hKmul : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, x * y ∈ I.Kset` using `fun x hx y hy => (Inhab.mem_Ksub I _).mp ((Inhab.Ksub I).mul_mem ((Inhab.mem_Ksub I x).mpr hx) ((Inhab.mem_Ksub I y).mpr hy))`. Establish `hone : ∀ x ∈ I.Kset, ∀ kv : (Σ k, Pl k), (fr kv.1 kv.2).ActsAs x 1 → ρ x kv = 1` using `fun x hx kv h => val_eq_lemma hρ hx kv (M := 1) (by rw [Units.val_one]; exact h)`.

Establish `: Fintype (Σ k, Pl k)` using `Fintype.ofFinite _`. Use `⟨⟨ρ, hmul, fun x hx => ?_, fun q => ?_⟩, hρ⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.T.trivial_mod_chosen_primes_iff_mem_Kg I N g Pl w fr hn hc x hx]`. Prove the components needed by the constructor for the conclusion. Introduce `h1 k v y h`.

Rewrite using `[hρ x hx k v y h, h1]`. Simplify using the standard rewrite rules. Introduce `h`. Use function extensionality and compare the values at `kv`. Conclude with `hone x hx kv (fun y hy => by rw [h kv.1 kv.2 y hy, Matrix.one_mulVec])`.

Establish `key : ∀ s : Finset (Σ k, Pl k), ∃ x ∈ I.Kset, ρ x = fun kv => if kv ∈ s then q kv else 1`. Introduce `s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Conclude with `⟨1, hK1, funext fun kv => by simpa using hone 1 hK1 kv (fr kv.1 kv.2).actsAs_one⟩`. Introduce `a s ha ih`.

Take `⟨xs, hxs, es⟩` from `ih`. Take `⟨xa, hxa, hact, hoth⟩` from `GlobalTheory.T.exists_mem_Kset_acts_as_GL_mod_splitPrime I N (g a.1) (w a.1 a.2) (fr a.1 a.2) hn (hc.1 a.1) (hc.2.2.2.1 a.1 a.2).2 (hc.2.2.2.2.2.1 a.1 a.2 a.2) (q a)`. Use `⟨xa * xs, hKmul xa hxa xs hxs, ?_⟩` and prove the remaining obligations. Rewrite using `[hmul xa hxa xs hxs, es]`. Use function extensionality and compare the values at `kv`.

Distinguish the cases in `hk : kv = a`. Rewrite using `[hk, Pi.mul_apply, val_eq_lemma hρ hxa a hact]`. Simplify using `[ha]`. Establish `hne` using `IsChoice.ne_of_ne hc hk`. Rewrite using `[Pi.mul_apply, hone xa hxa kv (PlFrame.actsAs_one_of_mem _ (hoth _ hne.1 hne.2))]`.

Simplify using `[hk]`. Take `⟨x, hx, e⟩` from `key Finset.univ`. Conclude with `⟨x, hx, by rw [e]; simp⟩`.
-/
theorem exists_red_actsBy : ∀ (I : AutInst) (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type)
    (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) (fr : ∀ k v, PlFrame I N (g k) (w k v)) [∀ k, Finite (Pl k)],
    I.n = N → IsChoice I g Pl w → ∃ ρ : Red I (g 0 * g 1) (GProd N g Pl), ActsBy fr ρ.toFun := by
  intro I N g Pl w fr _ hn hc
  classical
  obtain ⟨ρ, hρ, hmul⟩ := exists_actsBy fr
  have hK1 : (1 : I.Gf) ∈ I.Kset := (Inhab.mem_Ksub I 1).mp (Inhab.Ksub I).one_mem
  have hKmul : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, x * y ∈ I.Kset := fun x hx y hy =>
    (Inhab.mem_Ksub I _).mp
      ((Inhab.Ksub I).mul_mem ((Inhab.mem_Ksub I x).mpr hx) ((Inhab.mem_Ksub I y).mpr hy))
  have hone : ∀ x ∈ I.Kset, ∀ kv : (Σ k, Pl k), (fr kv.1 kv.2).ActsAs x 1 → ρ x kv = 1 :=
    fun x hx kv h => val_eq_lemma hρ hx kv (M := 1) (by rw [Units.val_one]; exact h)
  have : Fintype (Σ k, Pl k) := Fintype.ofFinite _
  refine ⟨⟨ρ, hmul, fun x hx => ?_, fun q => ?_⟩, hρ⟩
  · rw [← GlobalTheory.T.trivial_mod_chosen_primes_iff_mem_Kg I N g Pl w fr hn hc x hx]
    constructor
    · intro h1 k v y h
      rw [hρ x hx k v y h, h1]
      simp
    · intro h
      funext kv
      exact hone x hx kv (fun y hy => by rw [h kv.1 kv.2 y hy, Matrix.one_mulVec])
  · have key : ∀ s : Finset (Σ k, Pl k), ∃ x ∈ I.Kset, ρ x = fun kv => if kv ∈ s then q kv else 1 := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · exact ⟨1, hK1, funext fun kv => by simpa using hone 1 hK1 kv (fr kv.1 kv.2).actsAs_one⟩
      · intro a s ha ih
        obtain ⟨xs, hxs, es⟩ := ih
        obtain ⟨xa, hxa, hact, hoth⟩ := GlobalTheory.T.exists_mem_Kset_acts_as_GL_mod_splitPrime I N (g a.1) (w a.1 a.2) (fr a.1 a.2) hn (hc.1 a.1)
          (hc.2.2.2.1 a.1 a.2).2 (hc.2.2.2.2.2.1 a.1 a.2 a.2) (q a)
        refine ⟨xa * xs, hKmul xa hxa xs hxs, ?_⟩
        rw [hmul xa hxa xs hxs, es]
        funext kv
        by_cases hk : kv = a
        · rw [hk, Pi.mul_apply, val_eq_lemma hρ hxa a hact]
          simp [ha]
        · have hne := IsChoice.ne_of_ne hc hk
          rw [Pi.mul_apply, hone xa hxa kv (PlFrame.actsAs_one_of_mem _ (hoth _ hne.1 hne.2))]
          simp [hk]
    obtain ⟨x, hx, e⟩ := key Finset.univ
    exact ⟨x, hx, by rw [e]; simp⟩

end GlobalTheory.RowLev
