import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationWeilPairingEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionIsoOfGroupPullbackGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureTorsionPointsBijectiveStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.GenIso

/- English proof (translation)
Take `⟨ψ, hψ⟩` from `h1 (AlgHom.id K H)`. Establish `hψ' : ∀ a, ψ (f a) = a` using `fun a => congr($hψ a)`. Establish `e : f.comp ψ = AlgHom.id K H'` using `h2 (AlgHom.ext fun a => by show f (ψ (f a)) = f a`. Rewrite using `[hψ'])`. Use `⟨fun a b hab => ?_, fun b => ⟨ψ b, congr($e b)⟩⟩` and prove the remaining obligations.

Rewrite using `[← hψ' a, hab, hψ']`.
-/
theorem bijective_of_comp {K H H' : Type} [CommRing K] [CommRing H] [CommRing H'] [Algebra K H] [Algebra K H']
    (f : H →ₐ[K] H') (h1 : Function.Surjective fun ψ : H' →ₐ[K] H => ψ.comp f)
    (h2 : Function.Injective fun ψ : H' →ₐ[K] H' => ψ.comp f) : Function.Bijective f := by
  obtain ⟨ψ, hψ⟩ := h1 (AlgHom.id K H)
  have hψ' : ∀ a, ψ (f a) = a := fun a => congr($hψ a)
  have e : f.comp ψ = AlgHom.id K H' := h2 (AlgHom.ext fun a => by
    show f (ψ (f a)) = f a
    rw [hψ'])
  refine ⟨fun a b hab => ?_, fun b => ⟨ψ b, congr($e b)⟩⟩
  rw [← hψ' a, hab, hψ']

/- English proof (translation)
Introduce `p _ R K _ _ _ _ _ _ _ _ G _ _ _ G₀ _ _ F hF GG θ hθ GG₀ θ₀ hθ₀`. Use `letI alg : ∀ n, Algebra R (GG₀.A n) := fun n => ((algebraMap K (GG₀.A n)).comp (algebraMap R K)).toAlgebra`. Use `haveI tow : ∀ n, IsScalarTower R K (GG₀.A n) := fun n => .of_algebraMap_eq fun _ => rfl`. Establish `hu' : ∀ n, ∃ u : Tors G₀ (p ^ n) (GG₀.A n), θ₀.pt n _ u = AlgHom.id K _` using `fun n => (hθ₀ n _).2 _`. Use `choose u' hu' using hu'`.

Establish `hu : ∀ n, ∃ u : Tors G (p ^ n) (GG₀.A n), u.1.left = (u' n).1.left ≫ F` using `fun n => by`. Take `⟨τ, hτ⟩` from `GlobalTheory.T.torsion_iso_of_group_pullback_generic R K G G₀ F hF (p ^ n) (GG₀.A n)`. Conclude with `⟨τ (u' n), hτ _⟩`. Use `choose u hu using hu`. Set `g : ∀ n, GG.A n →ₐ[R] GG₀.A n` to `fun n => θ.pt n _ (u n)`.

Establish `compat : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower R K B] (z : Tors G (p ^ n) B) (z' : Tors G₀ (p ^ n) B), z.1.left = z'.1.left ≫ F → ∀ a, θ.pt n B z a = θ₀.pt n B z' (g n a)`. Introduce `n B _ _ _ _ z z' hz a`. Establish `h1 : torsMap (θ₀.pt n B z') (u' n) = z'` using `(hθ₀ n B).1 (by`. Rewrite using `[θ₀.nat n _ B (θ₀.pt n B z') (u' n) _ rfl, hu' n]`. Use the proof step `rfl)`.

Establish `h2 : z = torsMap ((θ₀.pt n B z').restrictScalars R) (u n)`. Use `Subtype.ext (Over.OverMorphism.ext ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[θ.nat n _ B ((θ₀.pt n B z').restrictScalars R) (u n) z (congrArg Subtype.val h2)]`. Both sides reduce to the same expression.

Establish `hp : p ≠ 0` using `(Fact.out : p.Prime).ne_zero`. Establish `hcounit : ∀ n (a : GG.A n), counit (R` using `K) (g n a) = algebraMap R K (counit a) := by`. Introduce `n a`. Take `⟨τ, hτ⟩` from `GlobalTheory.T.torsion_iso_of_group_pullback_generic R K G G₀ F hF (p ^ n) K`. Establish `h1` using `hτ 1`.

Rewrite `h1` using `[map_one]`. Establish `h2` using `compat n K 1 1 h1 a`. Establish `e1 : θ.pt n K 1 = (Algebra.ofId R K).comp (counitAlgHom R (GG.A n))` using `congrArg ofConv ((θ.pt_one n K hp).trans AlgHom.convOne_def)`. Establish `e2 : θ₀.pt n K 1 = (Algebra.ofId K K).comp (counitAlgHom K (GG₀.A n))` using `congrArg ofConv ((θ₀.pt_one n K hp).trans AlgHom.convOne_def)`. Rewrite `h2` using `[e1, e2]`.

Conclude with `h2.symm`. Establish `hmul : ∀ n (B : Type) [CommRing B] [Algebra R B] [Algebra K B], (∀ r, algebraMap R B r = algebraMap K B (algebraMap R K r)) → ∀ (x y : WithConv (GG₀.A n →ₐ[K] B)) (x₀ y₀ : WithConv (GG.A n →ₐ[R] B)), (∀ a, x₀.ofConv a = x.ofConv (g n a)) → (∀ a, y₀.ofConv a = y.ofConv (g n a)) → …`. Introduce `n B _ _ _ hB x y x₀ y₀ hx hy a`. Use `haveI : IsScalarTower R K B := .of_algebraMap_eq hB`. Take `⟨zx, hzx⟩` from `(hθ₀ n B).2 x.ofConv`.

Take `⟨zy, hzy⟩` from `(hθ₀ n B).2 y.ofConv`. Take `⟨τ, hτ⟩` from `GlobalTheory.T.torsion_iso_of_group_pullback_generic R K G G₀ F hF (p ^ n) B`. Establish `ex : x₀ = toConv (θ.pt n B (τ zx))` using `ofConv_injective (AlgHom.ext fun a => by`. Rewrite using `[hx, compat n B (τ zx) zx (hτ _) a, hzx])`. Establish `ey : y₀ = toConv (θ.pt n B (τ zy))` using `ofConv_injective (AlgHom.ext fun a => by`.

Rewrite using `[hy, compat n B (τ zy) zy (hτ _) a, hzy])`. Establish `exy : x = toConv (θ₀.pt n B zx)` using `by rw [hzx]`. Establish `eyy : y = toConv (θ₀.pt n B zy)` using `by rw [hzy]`. Rewrite using `[ex, ey, exy, eyy, ← θ.mul n B (τ zx) (τ zy) (τ (zx * zy)) (by rw [map_mul]; rfl), ← θ₀.mul n B zx zy (zx * zy) rfl]`. Conclude with `compat n B (τ (zx * zy)) (zx * zy) (hτ _) a`.

Establish `hres : ∀ n a, GG₀.res n (g (n + 1) a) = g n (GG.res n a)`. Introduce `n a`. Establish `hd : p ^ n ∣ p ^ (n + 1)` using `pow_dvd_pow p (Nat.le_succ n)`. Establish `h1` using `θ₀.res n (GG₀.A n) (u' n) (torsIncl hd (u' n)) rfl`. Establish `h2` using `θ.res n (GG₀.A n) (u n) (torsIncl hd (u n)) rfl`.

Establish `h3` using `compat (n + 1) (GG₀.A n) (torsIncl hd (u n)) (torsIncl hd (u' n)) (hu n) a`. Rewrite `h3` using `[h2, h1, hu' n]`. Conclude with `h3.symm`. Set `s : SemiHom (algebraMap R K) GG₀ GG` to `{ app := fun n => SemiBialgHom.ofPts (g n : GG.A n →+* GG₀.A n) (fun r => (g n).commutes r) (hcounit n) (hmul n) res_app := hres }`. Establish `hs : ∀ n a, s.lift.app n (1 ⊗ₜ a) = g n a` using `fun n a => (SemiHom.lift_app s n 1 a).trans (one_smul _ _)`.

Establish `hpre : ∀ n (B : Type) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower R K B], Function.Bijective fun ψ : GG₀.A n →ₐ[K] B => ψ.comp (s.lift.app n : K ⊗[R] GG.A n →ₐ[K] GG₀.A n)`. Introduce `n B _ _ _ _`. Take `⟨τ, hτ⟩` from `GlobalTheory.T.torsion_iso_of_group_pullback_generic R K G G₀ F hF (p ^ n) B`. Establish `hb` using `GlobalTheory.T.level_structure_torsion_points_bijective R K G (p ^ n) (GG.A n) (θ.level n) (hθ n) B`. Use `⟨fun ψ₁ ψ₂ h => ?_, fun χ => ?_⟩` and prove the remaining obligations.

Take `⟨z₁, rfl⟩` from `(hθ₀ n B).2 ψ₁`. Take `⟨z₂, rfl⟩` from `(hθ₀ n B).2 ψ₂`. Establish `h' : θ.pt n B (τ z₁) = θ.pt n B (τ z₂)` using `AlgHom.ext fun a => by`. Rewrite using `[compat n B _ z₁ (hτ _) a, compat n B _ z₂ (hτ _) a, ← hs]`. Conclude with `congr($h (1 ⊗ₜ a))`.

Rewrite using `[τ.injective (hb.1 h')]`. Take `⟨z, hz⟩` from `hb.2 ((χ.restrictScalars R).comp Algebra.TensorProduct.includeRight)`. Take `⟨z', rfl⟩` from `τ.surjective z`. Use `⟨θ₀.pt n B z', Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => ?_)⟩` and prove the remaining obligations. Use `show θ₀.pt n B z' (s.lift.app n (1 ⊗ₜ a)) = χ (1 ⊗ₜ a)`.

Rewrite using `[hs, ← compat n B _ z' (hτ _) a]`. Conclude with `congr($hz a)`. Establish `hbij : ∀ n, Function.Bijective (s.lift.app n)` using `fun n => bijective_of_comp (s.lift.app n : K ⊗[R] GG.A n →ₐ[K] GG₀.A n) (hpre n (K ⊗[R] GG.A n)).2 (hpre n (GG₀.A n)).1`. Use `⟨PDivGroup.isoOfBijective s.lift hbij, ?_⟩` and prove the remaining obligations. Introduce `n B _ _ _ _ z z' hz a`.

Rewrite using `[compat n B z z' hz a, isoOfBijective_hom, hs]`.
-/
theorem model_generic_iso : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G₀ : Over (Sp K)) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (spMap (algebraMap R K)) F → ∀ (GG : PDivGroup p R) (θ : TorsionMap G GG), IsModel K θ → ∀ (GG₀ : PDivGroup p K) (θ₀ : TorsionMap G₀ GG₀), (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra K B], Function.Bijective (θ₀.pt n B)) → ∃ e : GG₀ ≅ GG.baseChange K, GenCompat F θ θ₀ e := by
  intro p _ R K _ _ _ _ _ _ _ _ G _ _ _ G₀ _ _ F hF GG θ hθ GG₀ θ₀ hθ₀
  letI alg : ∀ n, Algebra R (GG₀.A n) := fun n => ((algebraMap K (GG₀.A n)).comp (algebraMap R K)).toAlgebra
  haveI tow : ∀ n, IsScalarTower R K (GG₀.A n) := fun n => .of_algebraMap_eq fun _ => rfl
  have hu' : ∀ n, ∃ u : Tors G₀ (p ^ n) (GG₀.A n), θ₀.pt n _ u = AlgHom.id K _ := fun n => (hθ₀ n _).2 _
  choose u' hu' using hu'
  have hu : ∀ n, ∃ u : Tors G (p ^ n) (GG₀.A n), u.1.left = (u' n).1.left ≫ F := fun n => by
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.torsion_iso_of_group_pullback_generic R K G G₀ F hF (p ^ n) (GG₀.A n)
    exact ⟨τ (u' n), hτ _⟩
  choose u hu using hu
  let g : ∀ n, GG.A n →ₐ[R] GG₀.A n := fun n => θ.pt n _ (u n)
  have compat : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower R K B]
      (z : Tors G (p ^ n) B) (z' : Tors G₀ (p ^ n) B), z.1.left = z'.1.left ≫ F → ∀ a,
      θ.pt n B z a = θ₀.pt n B z' (g n a) := by
    intro n B _ _ _ _ z z' hz a
    have h1 : torsMap (θ₀.pt n B z') (u' n) = z' := (hθ₀ n B).1 (by
      rw [θ₀.nat n _ B (θ₀.pt n B z') (u' n) _ rfl, hu' n]
      rfl)
    have h2 : z = torsMap ((θ₀.pt n B z').restrictScalars R) (u n) := by
      refine Subtype.ext (Over.OverMorphism.ext ?_)
      calc z.1.left = z'.1.left ≫ F := hz
        _ = (torsMap (θ₀.pt n B z') (u' n)).1.left ≫ F := by rw [h1]
        _ = spMap ((θ₀.pt n B z' : GG₀.A n →+* B)) ≫ ((u' n).1.left ≫ F) := Category.assoc _ _ _
        _ = _ := by rw [← hu n]; rfl
    rw [θ.nat n _ B ((θ₀.pt n B z').restrictScalars R) (u n) z (congrArg Subtype.val h2)]
    rfl
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hcounit : ∀ n (a : GG.A n), counit (R := K) (g n a) = algebraMap R K (counit a) := by
    intro n a
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.torsion_iso_of_group_pullback_generic R K G G₀ F hF (p ^ n) K
    have h1 := hτ 1
    rw [map_one] at h1
    have h2 := compat n K 1 1 h1 a
    have e1 : θ.pt n K 1 = (Algebra.ofId R K).comp (counitAlgHom R (GG.A n)) :=
      congrArg ofConv ((θ.pt_one n K hp).trans AlgHom.convOne_def)
    have e2 : θ₀.pt n K 1 = (Algebra.ofId K K).comp (counitAlgHom K (GG₀.A n)) :=
      congrArg ofConv ((θ₀.pt_one n K hp).trans AlgHom.convOne_def)
    rw [e1, e2] at h2
    exact h2.symm
  have hmul : ∀ n (B : Type) [CommRing B] [Algebra R B] [Algebra K B],
      (∀ r, algebraMap R B r = algebraMap K B (algebraMap R K r)) →
      ∀ (x y : WithConv (GG₀.A n →ₐ[K] B)) (x₀ y₀ : WithConv (GG.A n →ₐ[R] B)),
        (∀ a, x₀.ofConv a = x.ofConv (g n a)) → (∀ a, y₀.ofConv a = y.ofConv (g n a)) →
        ∀ a, (x₀ * y₀).ofConv a = (x * y).ofConv (g n a) := by
    intro n B _ _ _ hB x y x₀ y₀ hx hy a
    haveI : IsScalarTower R K B := .of_algebraMap_eq hB
    obtain ⟨zx, hzx⟩ := (hθ₀ n B).2 x.ofConv
    obtain ⟨zy, hzy⟩ := (hθ₀ n B).2 y.ofConv
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.torsion_iso_of_group_pullback_generic R K G G₀ F hF (p ^ n) B
    have ex : x₀ = toConv (θ.pt n B (τ zx)) := ofConv_injective (AlgHom.ext fun a => by
      rw [hx, compat n B (τ zx) zx (hτ _) a, hzx])
    have ey : y₀ = toConv (θ.pt n B (τ zy)) := ofConv_injective (AlgHom.ext fun a => by
      rw [hy, compat n B (τ zy) zy (hτ _) a, hzy])
    have exy : x = toConv (θ₀.pt n B zx) := by rw [hzx]
    have eyy : y = toConv (θ₀.pt n B zy) := by rw [hzy]
    rw [ex, ey, exy, eyy, ← θ.mul n B (τ zx) (τ zy) (τ (zx * zy)) (by rw [map_mul]; rfl),
      ← θ₀.mul n B zx zy (zx * zy) rfl]
    exact compat n B (τ (zx * zy)) (zx * zy) (hτ _) a
  have hres : ∀ n a, GG₀.res n (g (n + 1) a) = g n (GG.res n a) := by
    intro n a
    have hd : p ^ n ∣ p ^ (n + 1) := pow_dvd_pow p (Nat.le_succ n)
    have h1 := θ₀.res n (GG₀.A n) (u' n) (torsIncl hd (u' n)) rfl
    have h2 := θ.res n (GG₀.A n) (u n) (torsIncl hd (u n)) rfl
    have h3 := compat (n + 1) (GG₀.A n) (torsIncl hd (u n)) (torsIncl hd (u' n)) (hu n) a
    rw [h2, h1, hu' n] at h3
    exact h3.symm
  let s : SemiHom (algebraMap R K) GG₀ GG :=
    { app := fun n => SemiBialgHom.ofPts (g n : GG.A n →+* GG₀.A n) (fun r => (g n).commutes r) (hcounit n) (hmul n)
      res_app := hres }
  have hs : ∀ n a, s.lift.app n (1 ⊗ₜ a) = g n a := fun n a => (SemiHom.lift_app s n 1 a).trans (one_smul _ _)
  have hpre : ∀ n (B : Type) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower R K B],
      Function.Bijective fun ψ : GG₀.A n →ₐ[K] B => ψ.comp (s.lift.app n : K ⊗[R] GG.A n →ₐ[K] GG₀.A n) := by
    intro n B _ _ _ _
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.torsion_iso_of_group_pullback_generic R K G G₀ F hF (p ^ n) B
    have hb := GlobalTheory.T.level_structure_torsion_points_bijective R K G (p ^ n) (GG.A n) (θ.level n) (hθ n) B
    refine ⟨fun ψ₁ ψ₂ h => ?_, fun χ => ?_⟩
    · obtain ⟨z₁, rfl⟩ := (hθ₀ n B).2 ψ₁
      obtain ⟨z₂, rfl⟩ := (hθ₀ n B).2 ψ₂
      have h' : θ.pt n B (τ z₁) = θ.pt n B (τ z₂) := AlgHom.ext fun a => by
        rw [compat n B _ z₁ (hτ _) a, compat n B _ z₂ (hτ _) a, ← hs]
        exact congr($h (1 ⊗ₜ a))
      rw [τ.injective (hb.1 h')]
    · obtain ⟨z, hz⟩ := hb.2 ((χ.restrictScalars R).comp Algebra.TensorProduct.includeRight)
      obtain ⟨z', rfl⟩ := τ.surjective z
      refine ⟨θ₀.pt n B z', Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => ?_)⟩
      show θ₀.pt n B z' (s.lift.app n (1 ⊗ₜ a)) = χ (1 ⊗ₜ a)
      rw [hs, ← compat n B _ z' (hτ _) a]
      exact congr($hz a)
  have hbij : ∀ n, Function.Bijective (s.lift.app n) := fun n =>
    bijective_of_comp (s.lift.app n : K ⊗[R] GG.A n →ₐ[K] GG₀.A n) (hpre n (K ⊗[R] GG.A n)).2 (hpre n (GG₀.A n)).1
  refine ⟨PDivGroup.isoOfBijective s.lift hbij, ?_⟩
  intro n B _ _ _ _ z z' hz a
  rw [compat n B z z' hz a, isoOfBijective_hom, hs]

end GlobalTheory.GroupBplus.Aff.GenIso
