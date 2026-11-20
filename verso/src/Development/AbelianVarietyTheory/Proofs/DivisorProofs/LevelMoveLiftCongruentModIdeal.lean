import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvariance
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelMoveCong

open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, hx, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨c * a, fun v => mul_mem (hc v) (ha v), x, hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add y y' _ _ h h' => rw [smul_add]`. Conclude with `add_mem h h'`.

Consider the case `neg y _ h => rw [smul_neg]`. Conclude with `neg_mem h`.
-/
theorem intAdele_smul_mem_hat {n : ℕ} (S : Set (Fin n → E)) (c : FiniteAdeleRing (𝓞 F) F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) {z : Fin n → GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat F S) : (c ⊗ₜ[F] (1 : E)) • z ∈ GlobalTheory.AdLat.hat F S := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨c * a, fun v => mul_mem (hc v) (ha v), x, hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, hx, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨a, ha, t • x, Submodule.smul_mem_smul ht hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Both sides reduce to the same expression. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add y y' _ _ h h' => rw [smul_add]`.

Conclude with `add_mem h h'`. Consider the case `neg y _ h => rw [smul_neg]`. Conclude with `neg_mem h`.
-/
theorem ideal_smul_mem_hat {n : ℕ} (I : Ideal (𝓞 E)) (L : Submodule (𝓞 E) (Fin n → E)) {t : 𝓞 E} (ht : t ∈ I)
    {z : Fin n → GlobalTheory.AdLat.RA F E} (hz : z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (t : E)) • z ∈
      GlobalTheory.AdLat.hat F ((I • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a, ha, t • x, Submodule.smul_mem_smul ht hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, map_natCast]`. Rewrite using `[← Algebra.TensorProduct.includeRight_apply, map_natCast]`.
-/
theorem nsmul_eq_smul {n : ℕ} (M : ℕ) (w : Fin n → GlobalTheory.AdLat.RA F E) :
    M • w = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((M : 𝓞 E) : E))) • w := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, map_natCast]
  rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]

/- English proof (translation)
Use `conv_lhs => rw [h]`. Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_smul, smul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem split_sub {n : ℕ} (K : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (x y : Fin n → GlobalTheory.AdLat.RA F E)
    (r : GlobalTheory.AdLat.RA F E) (h : x = y + r • x) :
    K *ᵥ x - x = (K *ᵥ y - y) + r • (K *ᵥ x - x) := by
  conv_lhs => rw [h]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, smul_sub]
  abel

/- English proof (translation)
Establish `e : (fun i => c ⊗ₜ[F] x i) = (c ⊗ₜ[F] (1 : E)) • GlobalTheory.AdLat.fv F x`. Use function extensionality and compare the values at `i`. Simplify using `[GlobalTheory.AdLat.fv, Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[e, Matrix.mulVec_smul, smul_sub]`.
-/
theorem gen_sub {n : ℕ} (K : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (c : FiniteAdeleRing (𝓞 F) F)
    (x : Fin n → E) :
    K *ᵥ (fun i => c ⊗ₜ[F] x i) - (fun i => c ⊗ₜ[F] x i) =
      (c ⊗ₜ[F] (1 : E)) • (K *ᵥ GlobalTheory.AdLat.fv F x - GlobalTheory.AdLat.fv F x) := by
  have e : (fun i => c ⊗ₜ[F] x i) = (c ⊗ₜ[F] (1 : E)) • GlobalTheory.AdLat.fv F x := by
    funext i; simp [GlobalTheory.AdLat.fv, Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, Matrix.mulVec_smul, smul_sub]

end Gen

end GlobalTheory.LevelMoveCong

namespace GlobalTheory.LevelMoveCong

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D V La _ _ ι hι M Mb Mh hsup hM κ hκ f hf hfb z hz`. Use `set K := (Formalism.L2.Theta.finHom V κ).1 with hKdef`. Use `set L' := Formalism.L2.Pj.latG V 1 with hL'`. Use `set P := GlobalTheory.AdLat.hat D.host.F ((Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) with hP`. Establish `hhat1 : Formalism.L2.Pj.latGHat V 1 = GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E))` using `(GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1`.

Establish `hK : ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)), K *ᵥ y ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E))`. Introduce `y hy`. Establish `h4` using `(GlobalTheory.Member.latG_lattice_and_completion D V κ).2.2.2.1`. Establish `he` using `GlobalTheory.Member.LatMove.hat_eq_of_finCong V hκ`. Establish `h5 : K *ᵥ y ∈ (Formalism.L2.Pj.latGHat V κ : Set _)` using `by rw [h4]; exact ⟨y, hy, rfl⟩`.

Rewrite `h5` using `[he, hhat1]`. Conclude with `h5`. Establish `hone : ∀ v, (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) v ∈ v.adicCompletionIntegers D.host.F` using `fun v => one_mem _`. Establish `hfv : ∀ u ∈ L', Formalism.L2.Pj.finVec V u ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E))` using `fun u hu => AddSubgroup.subset_closure ⟨1, hone, u, hu, rfl⟩`. Establish `hfvP : ∀ u ∈ (Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.L2.Pj.finVec V u ∈ P` using `fun u hu => AddSubgroup.subset_closure ⟨1, hone, u, hu, rfl⟩`.

Take `⟨b, hb, m, hm, hmb⟩ : ∃ b ∈ Mb, ∃ m ∈ Mh, b + m = 1` from `Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top)`. Establish `hfv_sub : ∀ u u', Formalism.L2.Pj.finVec V (u - u') = Formalism.L2.Pj.finVec V u - Formalism.L2.Pj.finVec V u'`. Introduce `u u'`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.L2.Pj.finVec, TensorProduct.tmul_sub]`.

Establish `hrange : ∀ x ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La), ι x ∈ (Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))`. Introduce `x hx`. Establish `h1 : ι x ∈ (Mb • (⊤ : Submodule (𝓞 D.host.E) La)).map ι` using `Submodule.mem_map_of_mem hx`. Rewrite `h1` using `[Submodule.map_smul'', Submodule.map_top, hι.2]`. Then use the resulting hypothesis. Establish `step1 : ∀ v : La, K *ᵥ Formalism.L2.Pj.finVec V (ι (m • v)) - Formalism.L2.Pj.finVec V (ι (m • v)) ∈ P`.

Introduce `v`. Take `⟨w, hw, hw'⟩` from `hf (m • v) (Submodule.smul_mem_smul hm Submodule.mem_top)`. Establish `e : K *ᵥ Formalism.L2.Pj.finVec V (ι (m • v)) - Formalism.L2.Pj.finVec V (ι (m • v)) = Formalism.L2.Pj.finVec V (ι (f (m • v) - m • v)) - M • w`. Rewrite using `[map_sub, hfv_sub, ← hw']`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Use `sub_mem (hfvP _ (hrange _ (hfb _))) ?_` and prove the remaining obligations. Rewrite `hw` using `[hhat1]`. Rewrite using `[nsmul_eq_smul]`. Conclude with `ideal_smul_mem_hat Mb L' hM hw`.

Establish `step2 : ∀ u ∈ L', K *ᵥ Formalism.L2.Pj.finVec V u - Formalism.L2.Pj.finVec V u ∈ P`. Introduce `u hu`. Establish `hu' : u ∈ LinearMap.range ι` using `by rw [hι.2]; exact hu`. Take `⟨v, rfl⟩` from `hu'`. Establish `hsplit : Formalism.L2.Pj.finVec V (ι v) = Formalism.L2.Pj.finVec V (ι (m • v)) + ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((b : 𝓞 D.host.E) : D.host.E)) • Formalism.L2.Pj.finVec V (ι v)`.

Use function extensionality and compare the values at `i`. Simplify using `only [Formalism.L2.Pj.finVec, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[← TensorProduct.tmul_add]`. Use `congr 1`. Rewrite using `[Algebra.smul_def, ← add_mul]`.

Establish `: ((algebraMap (𝓞 D.host.E) D.host.E m) + (b : D.host.E)) = 1` using `by show ((m : D.host.E)) + (b : D.host.E) = 1`. Rewrite using `[add_comm]`. Conclude with `congrArg ((↑) : 𝓞 D.host.E → D.host.E) hmb` after adjusting the coercions. Rewrite using `[this, one_mul]`. Rewrite using `[split_sub K _ _ _ hsplit]`.

Use `add_mem (step1 v) (ideal_smul_mem_hat Mb L' hb ?_)` and prove the remaining obligations. Establish `hu : ι v ∈ L'` using `by rw [hL', ← hι.2]; exact ⟨v, rfl⟩`. Conclude with `sub_mem (hK _ (hfv _ hu)) (hfv _ hu)`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem y hy`.

Take `⟨c, hc, x, hx, rfl⟩` from `hy`. Rewrite using `[gen_sub K c x]`. Conclude with `intAdele_smul_mem_hat _ c hc (step2 x hx)`. Consider the case `zero => rw [Matrix.mulVec_zero, sub_zero]`. Conclude with `zero_mem _`.

Consider the case `add y y' _ _ h h'`. Establish `e : K *ᵥ (y + y') - (y + y') = (K *ᵥ y - y) + (K *ᵥ y' - y')`. Rewrite using `[Matrix.mulVec_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `add_mem h h'`. Consider the case `neg y _ h`. Establish `e : K *ᵥ (-y) - (-y) = -(K *ᵥ y - y)`. Rewrite using `[Matrix.mulVec_neg]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `neg_mem h`.
-/
theorem mulVec_sub_mem_hat_smul : ∀ {D : D7} (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), Formalism.L2.Pj.LatEmb V ι → ∀ (M : ℕ) (Mb Mh : Ideal (𝓞 D.host.E)), Mb ⊔ Mh = ⊤ → ((M : ℕ) : 𝓞 D.host.E) ∈ Mb → ∀ (κ : Formalism.L2.Theta.GA D V), GlobalTheory.Member.FinCong V 1 κ → ∀ (f : La →ₗ[𝓞 D.host.E] La), (∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ Formalism.L2.Pj.latGHat V 1, Formalism.L2.Pj.finVec V (ι (f a)) - (Formalism.L2.Theta.finHom V κ).1 *ᵥ Formalism.L2.Pj.finVec V (ι a) = M • w) → (∀ x, f x - x ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La)) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), (Formalism.L2.Theta.finHom V κ).1 *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((Mb • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  intro D V La _ _ ι hι M Mb Mh hsup hM κ hκ f hf hfb z hz
  set K := (Formalism.L2.Theta.finHom V κ).1 with hKdef
  set L' := Formalism.L2.Pj.latG V 1 with hL'
  set P := GlobalTheory.AdLat.hat D.host.F ((Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    Set (Fin V.rank → D.host.E)) with hP
  have hhat1 : Formalism.L2.Pj.latGHat V 1 = GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1
  have hK : ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)),
      K *ᵥ y ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) := by
    intro y hy
    have h4 := (GlobalTheory.Member.latG_lattice_and_completion D V κ).2.2.2.1
    have he := GlobalTheory.Member.LatMove.hat_eq_of_finCong V hκ
    have h5 : K *ᵥ y ∈ (Formalism.L2.Pj.latGHat V κ : Set _) := by rw [h4]; exact ⟨y, hy, rfl⟩
    rw [he, hhat1] at h5
    exact h5
  have hone : ∀ v, (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) v ∈ v.adicCompletionIntegers D.host.F :=
    fun v => one_mem _
  have hfv : ∀ u ∈ L', Formalism.L2.Pj.finVec V u ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) :=
    fun u hu => AddSubgroup.subset_closure ⟨1, hone, u, hu, rfl⟩
  have hfvP : ∀ u ∈ (Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.L2.Pj.finVec V u ∈ P :=
    fun u hu => AddSubgroup.subset_closure ⟨1, hone, u, hu, rfl⟩
  obtain ⟨b, hb, m, hm, hmb⟩ : ∃ b ∈ Mb, ∃ m ∈ Mh, b + m = 1 :=
    Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top)
  have hfv_sub : ∀ u u', Formalism.L2.Pj.finVec V (u - u') = Formalism.L2.Pj.finVec V u - Formalism.L2.Pj.finVec V u' := by
    intro u u'; funext i; simp [Formalism.L2.Pj.finVec, TensorProduct.tmul_sub]
  have hrange : ∀ x ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La),
      ι x ∈ (Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) := by
    intro x hx
    have h1 : ι x ∈ (Mb • (⊤ : Submodule (𝓞 D.host.E) La)).map ι := Submodule.mem_map_of_mem hx
    rwa [Submodule.map_smul'', Submodule.map_top, hι.2] at h1

  have step1 : ∀ v : La, K *ᵥ Formalism.L2.Pj.finVec V (ι (m • v)) - Formalism.L2.Pj.finVec V (ι (m • v)) ∈ P := by
    intro v
    obtain ⟨w, hw, hw'⟩ := hf (m • v) (Submodule.smul_mem_smul hm Submodule.mem_top)
    have e : K *ᵥ Formalism.L2.Pj.finVec V (ι (m • v)) - Formalism.L2.Pj.finVec V (ι (m • v)) =
        Formalism.L2.Pj.finVec V (ι (f (m • v) - m • v)) - M • w := by
      rw [map_sub, hfv_sub, ← hw']; abel
    rw [e]
    refine sub_mem (hfvP _ (hrange _ (hfb _))) ?_
    rw [hhat1] at hw
    rw [nsmul_eq_smul]
    exact ideal_smul_mem_hat Mb L' hM hw

  have step2 : ∀ u ∈ L', K *ᵥ Formalism.L2.Pj.finVec V u - Formalism.L2.Pj.finVec V u ∈ P := by
    intro u hu
    have hu' : u ∈ LinearMap.range ι := by rw [hι.2]; exact hu
    obtain ⟨v, rfl⟩ := hu'
    have hsplit : Formalism.L2.Pj.finVec V (ι v) = Formalism.L2.Pj.finVec V (ι (m • v)) +
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((b : 𝓞 D.host.E) : D.host.E)) •
          Formalism.L2.Pj.finVec V (ι v) := by
      funext i
      simp only [Formalism.L2.Pj.finVec, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [← TensorProduct.tmul_add]
      congr 1
      rw [Algebra.smul_def, ← add_mul]
      have : ((algebraMap (𝓞 D.host.E) D.host.E m) + (b : D.host.E)) = 1 := by
        show ((m : D.host.E)) + (b : D.host.E) = 1
        rw [add_comm]; exact_mod_cast congrArg ((↑) : 𝓞 D.host.E → D.host.E) hmb
      rw [this, one_mul]
    rw [split_sub K _ _ _ hsplit]
    refine add_mem (step1 v) (ideal_smul_mem_hat Mb L' hb ?_)
    have hu : ι v ∈ L' := by rw [hL', ← hι.2]; exact ⟨v, rfl⟩
    exact sub_mem (hK _ (hfv _ hu)) (hfv _ hu)

  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hy
    rw [gen_sub K c x]
    exact intAdele_smul_mem_hat _ c hc (step2 x hx)
  | zero => rw [Matrix.mulVec_zero, sub_zero]; exact zero_mem _
  | add y y' _ _ h h' =>
    have e : K *ᵥ (y + y') - (y + y') = (K *ᵥ y - y) + (K *ᵥ y' - y') := by
      rw [Matrix.mulVec_add]; abel
    rw [e]; exact add_mem h h'
  | neg y _ h =>
    have e : K *ᵥ (-y) - (-y) = -(K *ᵥ y - y) := by
      rw [Matrix.mulVec_neg]; abel
    rw [e]; exact neg_mem h

end GlobalTheory.LevelMoveCong
