import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivHomDivisibleByPowOfKillsPowTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomSurjectiveIffFinrankKernelQuotientEqOneStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

section

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

/- English proof (translation)
Proceed by induction on `a generalizing X Y with`. Consider the case `zero => simpa using h`. Consider the case `succ a ih`. Apply `ih` to reduce the goal to its premises. Rewrite using `[← sub_eq_zero, ← smul_sub]`.

Apply `eq_zero_of_prime_smul_eq_zero` to reduce the goal to its premises. Rewrite using `[smul_smul, ← pow_succ', smul_sub, h, sub_self]`.
-/
theorem pow_smul_cancel {G H : PDivGroup p k} (a : ℕ) {X Y : G ⟶ H}
    (h : (p : ℤ_[p]) ^ a • X = (p : ℤ_[p]) ^ a • Y) : X = Y := by
  induction a generalizing X Y with
  | zero => simpa using h
  | succ a ih =>
    apply ih
    rw [← sub_eq_zero, ← smul_sub]
    apply eq_zero_of_prime_smul_eq_zero
    rw [smul_smul, ← pow_succ', smul_sub, h, sub_self]

/- English proof (translation)
Establish `h` using `G.rank_eq n ⟨⊥, Ideal.isPrime_bot⟩`. Simplify `h` using `[Module.rankAtStalk_eq_finrank_of_free]`.
-/
theorem finrank_A (G : PDivGroup p k) (n : ℕ) : Module.finrank k (G.A n) = p ^ (n * G.height) := by
  have h := G.rank_eq n ⟨⊥, Ideal.isPrime_bot⟩
  simpa [Module.rankAtStalk_eq_finrank_of_free] using h

/- English proof (translation)
Assemble the required witnesses or components as `⟨m, 𝟙 G, Category.comp_id _, Category.id_comp _⟩`.
-/
theorem isIsog_pow_smul_id (G : PDivGroup p k) (m : ℕ) : IsIsog ((p : ℤ_[p]) ^ m • 𝟙 G) :=
  ⟨m, 𝟙 G, Category.comp_id _, Category.id_comp _⟩

/- English proof (translation)
Use `⟨m, fun n hn => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, hk⟩` from `G.exists_res_le hn`. Establish `e : Hom.app ((p : ℤ_[p]) ^ m • 𝟙 G) n = mulBy k _ (p ^ m)`. Rewrite using `[← Nat.cast_pow, natCast_smul_id_app]`. Rewrite using `[e]`.

Express the relevant statement in the definitionally equal form `Module.finrank k (G.A n ⧸ torsionIdeal k (G.A n) (p ^ m)) = _`. Rewrite using `[← hk]`. Conclude with `((Ideal.quotientKerAlgEquivOfSurjective (f := (f : G.A n →ₐ[k] G.A m)) hf).toLinearEquiv.finrank_eq).trans (finrank_A G m)`.
-/
theorem hasLogDeg_pow_smul_id (G : PDivGroup p k) (m : ℕ) :
    HasLogDeg ((p : ℤ_[p]) ^ m • 𝟙 G) (m * G.height) := by
  refine ⟨m, fun n hn => ?_⟩
  obtain ⟨f, hf, hk⟩ := G.exists_res_le hn
  have e : Hom.app ((p : ℤ_[p]) ^ m • 𝟙 G) n = mulBy k _ (p ^ m) := by
    rw [← Nat.cast_pow, natCast_smul_id_app]
  rw [e]
  change Module.finrank k (G.A n ⧸ torsionIdeal k (G.A n) (p ^ m)) = _
  rw [← hk]
  exact ((Ideal.quotientKerAlgEquivOfSurjective (f := (f : G.A n →ₐ[k] G.A m)) hf).toLinearEquiv.finrank_eq).trans
    (finrank_A G m)

/- English proof (translation)
Take `⟨a, f', h1, h2⟩` from `hf`. Take `⟨b, g', h3, h4⟩` from `hg`. Use `⟨a + b, g' ≫ f', ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h3, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h1, smul_smul, ← pow_add, add_comm b a]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h4, smul_smul, ← pow_add]`.
-/
theorem isIsog_comp {G H K : PDivGroup p k} {f : G ⟶ H} {g : H ⟶ K} (hf : IsIsog f)
    (hg : IsIsog g) : IsIsog (f ≫ g) := by
  obtain ⟨a, f', h1, h2⟩ := hf
  obtain ⟨b, g', h3, h4⟩ := hg
  refine ⟨a + b, g' ≫ f', ?_, ?_⟩
  · calc (f ≫ g) ≫ g' ≫ f' = f ≫ (g ≫ g') ≫ f' := by simp only [Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 G := by
        rw [h3, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h1, smul_smul, ← pow_add,
          add_comm b a]
  · calc (g' ≫ f') ≫ f ≫ g = g' ≫ (f' ≫ f) ≫ g := by simp only [Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 K := by
        rw [h2, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h4, smul_smul, ← pow_add]

/- English proof (translation)
Take `⟨a, f', h1, h2⟩` from `hf`. Take `⟨b, u, h3, h4⟩` from `hfg`. Use `⟨a + b, (p : ℤ_[p]) ^ a • (u ≫ f), ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Linear.comp_smul, Linear.smul_comp, Category.id_comp]`.

Use `_ = f' ≫ ((f ≫ g) ≫ u) ≫ f := by rw [← h2]; simp only [Category.assoc]`. Use `_ = (p : ℤ_[p]) ^ (a + b) • 𝟙 H := by`. Rewrite using `[h3, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h2, smul_smul, ← pow_add, add_comm b a]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Linear.smul_comp, Category.assoc]`.

Use `_ = (p : ℤ_[p]) ^ (a + b) • 𝟙 K := by rw [h4, smul_smul, ← pow_add]`.
-/
theorem isIsog_of_comp {G H K : PDivGroup p k} {f : G ⟶ H} {g : H ⟶ K} (hf : IsIsog f)
    (hfg : IsIsog (f ≫ g)) : IsIsog g := by
  obtain ⟨a, f', h1, h2⟩ := hf
  obtain ⟨b, u, h3, h4⟩ := hfg
  refine ⟨a + b, (p : ℤ_[p]) ^ a • (u ≫ f), ?_, ?_⟩
  · calc g ≫ ((p : ℤ_[p]) ^ a • (u ≫ f)) = ((p : ℤ_[p]) ^ a • 𝟙 H) ≫ g ≫ u ≫ f := by
          rw [Linear.comp_smul, Linear.smul_comp, Category.id_comp]
      _ = f' ≫ ((f ≫ g) ≫ u) ≫ f := by rw [← h2]; simp only [Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 H := by
        rw [h3, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h2, smul_smul, ← pow_add,
          add_comm b a]
  · calc ((p : ℤ_[p]) ^ a • (u ≫ f)) ≫ g = (p : ℤ_[p]) ^ a • (u ≫ f ≫ g) := by
          rw [Linear.smul_comp, Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 K := by rw [h4, smul_smul, ← pow_add]

variable [CharP k p]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨N, hN⟩`. Take `⟨a, f', h1, h2⟩` from `hf`. Establish `hs : Function.Surjective (f.app (N + a))` using `(GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one k (G.A (N + a)) (H.A (N + a)) (f.app (N + a))).2 ((hN (N + a) (Nat.le_add_right N a)).trans (pow_zero p))`. Use `set f'' : H ⟶ G := (p : ℤ_[p]) ^ N • f' with hf''`.

Establish `e1 : f ≫ f'' = (p : ℤ_[p]) ^ (N + a) • 𝟙 G`. Rewrite using `[hf'', Linear.comp_smul, h1, smul_smul, ← pow_add]`. Establish `e2 : f'' ≫ f = (p : ℤ_[p]) ^ (N + a) • 𝟙 H`. Rewrite using `[hf'', Linear.smul_comp, h2, smul_smul, ← pow_add]`. Establish `hc : f''.conv (N + a) = 1`.

Establish `h3 : precomp (H.A (N + a)) (f.app (N + a)) (f''.conv (N + a)) = precomp (H.A (N + a)) (f.app (N + a)) 1`. Rewrite using `[map_one, ← comp_conv_left, e2, pow_smul_conv]`. Use `WithConv.ofConv_injective (BialgHom.ext fun x => ?_)` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hs x`. Conclude with `DFunLike.congr_fun (congrArg WithConv.ofConv h3) y`.

Take `⟨g, hg⟩` from `GlobalTheory.T.pDivHom_divisible_by_pow_of_kills_pow_torsion p k H G (N + a) f'' hc`. Use `⟨⟨g, ?_, ?_⟩⟩` and prove the remaining obligations. Use `pow_smul_cancel (N + a) ?_` and prove the remaining obligations. Rewrite using `[← Linear.comp_smul, ← hg, e1]`. Use `pow_smul_cancel (N + a) ?_` and prove the remaining obligations.

Rewrite using `[← Linear.smul_comp, ← hg, e2]`. Introduce `hi`. Use `⟨0, fun n _ => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero]`. Use `(GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one k (G.A n) (H.A n) (f.app n)).1 fun x => ⟨(inv f).app n x, ?_⟩` and prove the remaining obligations.

Establish `h` using `congrArg (fun φ : G ⟶ G => φ.app n x) (IsIso.hom_inv_id f)`. Conclude with `h`.
-/
theorem hasLogDeg_zero_iff_isIso {G H : PDivGroup p k} (f : G ⟶ H) (hf : IsIsog f) :
    HasLogDeg f 0 ↔ IsIso f := by
  constructor
  · rintro ⟨N, hN⟩
    obtain ⟨a, f', h1, h2⟩ := hf
    have hs : Function.Surjective (f.app (N + a)) :=
      (GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one k (G.A (N + a)) (H.A (N + a)) (f.app (N + a))).2
        ((hN (N + a) (Nat.le_add_right N a)).trans (pow_zero p))
    set f'' : H ⟶ G := (p : ℤ_[p]) ^ N • f' with hf''
    have e1 : f ≫ f'' = (p : ℤ_[p]) ^ (N + a) • 𝟙 G := by
      rw [hf'', Linear.comp_smul, h1, smul_smul, ← pow_add]
    have e2 : f'' ≫ f = (p : ℤ_[p]) ^ (N + a) • 𝟙 H := by
      rw [hf'', Linear.smul_comp, h2, smul_smul, ← pow_add]
    have hc : f''.conv (N + a) = 1 := by
      have h3 : precomp (H.A (N + a)) (f.app (N + a)) (f''.conv (N + a)) =
          precomp (H.A (N + a)) (f.app (N + a)) 1 := by
        rw [map_one, ← comp_conv_left, e2, pow_smul_conv]
      refine WithConv.ofConv_injective (BialgHom.ext fun x => ?_)
      obtain ⟨y, rfl⟩ := hs x
      exact DFunLike.congr_fun (congrArg WithConv.ofConv h3) y
    obtain ⟨g, hg⟩ := GlobalTheory.T.pDivHom_divisible_by_pow_of_kills_pow_torsion p k H G (N + a) f'' hc
    refine ⟨⟨g, ?_, ?_⟩⟩
    · refine pow_smul_cancel (N + a) ?_
      rw [← Linear.comp_smul, ← hg, e1]
    · refine pow_smul_cancel (N + a) ?_
      rw [← Linear.smul_comp, ← hg, e2]
  · intro hi
    refine ⟨0, fun n _ => ?_⟩
    rw [pow_zero]
    refine (GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one k (G.A n) (H.A n) (f.app n)).1 fun x => ⟨(inv f).app n x, ?_⟩
    have h := congrArg (fun φ : G ⟶ G => φ.app n x) (IsIso.hom_inv_id f)
    exact h

/- English proof (translation)
Introduce `_ _ _ _ _ G` and use `⟨fun m => ⟨isIsog_pow_smul_id G m, hasLogDeg_pow_smul_id G m⟩, fun _ _ _ _ => isIsog_comp, fun _ _ _ _ => isIsog_of_comp, fun _ f => hasLogDeg_zero_iff_isIso f⟩`.
-/
theorem isog_basics : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G : PDivGroup p k),
    (∀ m : ℕ, IsIsog ((p : ℤ_[p]) ^ m • 𝟙 G) ∧ HasLogDeg ((p : ℤ_[p]) ^ m • 𝟙 G) (m * G.height)) ∧
    (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog g → IsIsog (f ≫ g)) ∧
    (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog (f ≫ g) → IsIsog g) ∧
    ∀ (H : PDivGroup p k) (f : G ⟶ H), IsIsog f → (HasLogDeg f 0 ↔ IsIso f) :=
  fun _ _ _ _ _ G => ⟨fun m => ⟨isIsog_pow_smul_id G m, hasLogDeg_pow_smul_id G m⟩,
    fun _ _ _ _ => isIsog_comp, fun _ _ _ _ => isIsog_of_comp,
    fun _ f => hasLogDeg_zero_iff_isIso f⟩

end

end GlobalTheory.Dieu
