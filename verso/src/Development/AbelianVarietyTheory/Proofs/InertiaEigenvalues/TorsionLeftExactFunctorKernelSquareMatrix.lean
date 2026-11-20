import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorsOfCardHomResidueFieldLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatibleGeneratorsTowerLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChainLeIInfSupPowSmulTopOfPrecompleteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionModuleExtendingResidueMapsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftExactFunctorRepresentableTorsionModulesStatement

noncomputable section

open IsLocalRing CategoryTheory GlobalTheory.SelFun Formalism.MainNotions.BlochKatoReduction

namespace GlobalTheory.KRep

/- English proof (translation)
Use `choose g hg using tot`. Set `f : X →ₗ[Λ] Y` to `{ toFun := g map_add' := fun x x' => fn _ _ _ (hg (x + x')) (add _ _ _ _ (hg x) (hg x')) map_smul' := fun c x => fn _ _ _ (hg (c • x)) (smul c _ _ (hg x)) }`. Establish `hbij : Function.Bijective f`. Use `⟨fun x x' h => inj x x' (g x) (hg x) ?_, fun y => ?_⟩` and prove the remaining obligations. Establish `h' : g x = g x'` using `h`.

Rewrite using `[h']`. Conclude with `hg x'`. Take `⟨x, hx⟩` from `sur y`. Conclude with `⟨x, fn _ _ _ (hg x) hx⟩`. Conclude with `⟨LinearEquiv.ofBijective f hbij, hg⟩`.
-/
theorem exists_equiv_of_rel {Λ X Y : Type} [CommRing Λ] [AddCommGroup X] [Module Λ X] [AddCommGroup Y] [Module Λ Y]
    (R : X → Y → Prop) (tot : ∀ x, ∃ y, R x y) (fn : ∀ x y y', R x y → R x y' → y = y')
    (inj : ∀ x x' y, R x y → R x' y → x = x') (sur : ∀ y, ∃ x, R x y)
    (add : ∀ x x' y y', R x y → R x' y' → R (x + x') (y + y')) (smul : ∀ (c : Λ) x y, R x y → R (c • x) (c • y)) :
    ∃ e : X ≃ₗ[Λ] Y, ∀ x, R x (e x) := by
  choose g hg using tot
  let f : X →ₗ[Λ] Y :=
    { toFun := g
      map_add' := fun x x' => fn _ _ _ (hg (x + x')) (add _ _ _ _ (hg x) (hg x'))
      map_smul' := fun c x => fn _ _ _ (hg (c • x)) (smul c _ _ (hg x)) }
  have hbij : Function.Bijective f := by
    refine ⟨fun x x' h => inj x x' (g x) (hg x) ?_, fun y => ?_⟩
    · have h' : g x = g x' := h
      rw [h']
      exact hg x'
    · obtain ⟨x, hx⟩ := sur y
      exact ⟨x, fn _ _ _ (hg x) hx⟩
  exact ⟨LinearEquiv.ofBijective f hbij, hg⟩

def sol {Λ : Type} [CommRing Λ] {a : ℕ} (N : Submodule Λ (Fin a → Λ)) (B : Type) [AddCommGroup B] [Module Λ B] :
    Submodule Λ (Fin a → B) where
  carrier := {x | ∀ c ∈ N, ∑ i, c i • x i = 0}
  add_mem' := by
    intro x y hx hy c hc
    simp [smul_add, Finset.sum_add_distrib, hx c hc, hy c hc]
  zero_mem' := by intro c _; simp
  smul_mem' := by
    intro r x hx c hc
    have : ∑ i, c i • (r • x) i = r • ∑ i, c i • x i := by
      simp [Finset.smul_sum, smul_comm r]
    rw [this, hx c hc, smul_zero]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_sol {Λ : Type} [CommRing Λ] {a : ℕ} {N : Submodule Λ (Fin a → Λ)} {B : Type} [AddCommGroup B] [Module Λ B]
    {x : Fin a → B} : x ∈ sol N B ↔ ∀ c ∈ N, ∑ i, c i • x i = 0 := Iff.rfl

/- English proof (translation)
Establish `hc : c = ∑ i, c i • (Pi.single i (1 : Λ) : Fin a → Λ)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [hc]`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul]`.
-/
theorem lin_eq_sum {Λ : Type} [CommRing Λ] {a : ℕ} {B : Type} [AddCommGroup B] [Module Λ B]
    (u : (Fin a → Λ) →ₗ[Λ] B) (c : Fin a → Λ) : u c = ∑ i, c i • u (Pi.single i 1) := by
  have hc : c = ∑ i, c i • (Pi.single i (1 : Λ) : Fin a → Λ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hc]
  rw [map_sum]
  simp only [map_smul]

variable {Λ : Type} [CommRing Λ] [IsLocalRing Λ]

/- English proof (translation)
Use `choose k hk using fun i => hB (x i)`. Consider the cases of `nonempty_fintype ι`. Use `⟨∑ i, k i, fun r hr i => hk i r (Ideal.pow_le_pow_right ?_ hr)⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_pow_kill {B : Type} [AddCommGroup B] [Module Λ B] (hB : Tors Λ B) {ι : Type} [Finite ι] (x : ι → B) :
    ∃ n : ℕ, ∀ r ∈ maximalIdeal Λ ^ (n + 1), ∀ i, r • x i = 0 := by
  choose k hk using fun i => hB (x i)
  cases nonempty_fintype ι
  refine ⟨∑ i, k i, fun r hr i => hk i r (Ideal.pow_le_pow_right ?_ hr)⟩
  calc k i ≤ ∑ j, k j := Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
    _ ≤ ∑ j, k j + 1 := Nat.le_succ _

/- English proof (translation)
Take `⟨T, hT⟩` from `hS`. Take `⟨n, hn⟩` from `exists_pow_kill hB (fun t : T => (t : B))`. Establish `hn' : ∀ r ∈ maximalIdeal Λ ^ (n + 1), ∀ i : T, r • (i : B) = 0` using `hn`. Establish `hrange : Set.range (fun t : T => (t : B)) = (T : Set B)`. Use extensionality with `y`.

Simplify using the standard rewrite rules. Establish `hmem : ∀ i : T, (i : B) ∈ S`. Introduce `i`. Rewrite using `[← hT]`. Conclude with `Submodule.subset_span i.2`.

Establish `hspan : ∀ y ∈ S, ∃ c : T → Λ, ∑ i, c i • (i : B) = y`. Introduce `y hy`. Rewrite `hy` using `[← hT, ← hrange]`. Conclude with `(Submodule.mem_span_range_iff_exists_fun Λ).mp hy`. Establish `hkill : ∀ r ∈ maximalIdeal Λ ^ (n + 1), ∀ y : S, r • y = 0`.

Introduce `r hr y`. Take `⟨c, hc⟩` from `hspan y y.2`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_smul, ← hc, Finset.smul_sum, Submodule.coe_zero]`. Conclude with `Finset.sum_eq_zero fun i _ => by rw [smul_comm, hn' r hr i, smul_zero]`.

Establish `: Finite (Λ ⧸ maximalIdeal Λ)` using `‹Finite (ResidueField Λ)›`. Establish `: Finite (Λ ⧸ maximalIdeal Λ ^ (n + 1))` using `Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal Λ)) (n + 1)`. Use `⟨?_, n, hkill⟩` and prove the remaining obligations. Take `⟨s, hs⟩ : ∃ s : Λ ⧸ maximalIdeal Λ ^ (n + 1) → Λ, ∀ q, Ideal.Quotient.mk (maximalIdeal Λ ^ (n + 1)) (s q) = q` from `⟨Function.surjInv Ideal.Quotient.mk_surjective, Function.surjInv_eq Ideal.Quotient.mk_surjective⟩`. Use `Finite.of_surjective (fun q : T → Λ ⧸ maximalIdeal Λ ^ (n + 1) => (⟨∑ i, s (q i) • (i : B), S.sum_mem fun i _ => S.smul_mem _ (hmem i)⟩ : S)) ?_` and prove the remaining obligations.

Introduce `y`. Take `⟨c, hc⟩` from `hspan y y.2`. Use `⟨fun i => Ideal.Quotient.mk (maximalIdeal Λ ^ (n + 1)) (c i), Subtype.ext ?_⟩` and prove the remaining obligations. Use `show ∑ i, s (Ideal.Quotient.mk (maximalIdeal Λ ^ (n + 1)) (c i)) • (i : B) = y`. Rewrite using `[← hc, ← sub_eq_zero, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← sub_smul]`. Conclude with `hn' _ (Ideal.Quotient.eq.mp (hs _)) i`.
-/
theorem fg_finite [IsNoetherianRing Λ] [Finite (ResidueField Λ)] {B : Type} [AddCommGroup B] [Module Λ B] (hB : Tors Λ B)
    (S : Submodule Λ B) (hS : S.FG) : Finite S ∧ ∃ n : ℕ, ∀ r ∈ maximalIdeal Λ ^ (n + 1), ∀ y : S, r • y = 0 := by
  classical
  obtain ⟨T, hT⟩ := hS
  obtain ⟨n, hn⟩ := exists_pow_kill hB (fun t : T => (t : B))
  have hn' : ∀ r ∈ maximalIdeal Λ ^ (n + 1), ∀ i : T, r • (i : B) = 0 := hn
  have hrange : Set.range (fun t : T => (t : B)) = (T : Set B) := by
    ext y
    simp
  have hmem : ∀ i : T, (i : B) ∈ S := by
    intro i
    rw [← hT]
    exact Submodule.subset_span i.2
  have hspan : ∀ y ∈ S, ∃ c : T → Λ, ∑ i, c i • (i : B) = y := by
    intro y hy
    rw [← hT, ← hrange] at hy
    exact (Submodule.mem_span_range_iff_exists_fun Λ).mp hy
  have hkill : ∀ r ∈ maximalIdeal Λ ^ (n + 1), ∀ y : S, r • y = 0 := by
    intro r hr y
    obtain ⟨c, hc⟩ := hspan y y.2
    apply Subtype.ext
    rw [Submodule.coe_smul, ← hc, Finset.smul_sum, Submodule.coe_zero]
    exact Finset.sum_eq_zero fun i _ => by rw [smul_comm, hn' r hr i, smul_zero]
  have : Finite (Λ ⧸ maximalIdeal Λ) := ‹Finite (ResidueField Λ)›
  have : Finite (Λ ⧸ maximalIdeal Λ ^ (n + 1)) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal Λ)) (n + 1)
  refine ⟨?_, n, hkill⟩
  obtain ⟨s, hs⟩ : ∃ s : Λ ⧸ maximalIdeal Λ ^ (n + 1) → Λ,
      ∀ q, Ideal.Quotient.mk (maximalIdeal Λ ^ (n + 1)) (s q) = q :=
    ⟨Function.surjInv Ideal.Quotient.mk_surjective, Function.surjInv_eq Ideal.Quotient.mk_surjective⟩
  refine Finite.of_surjective (fun q : T → Λ ⧸ maximalIdeal Λ ^ (n + 1) =>
    (⟨∑ i, s (q i) • (i : B), S.sum_mem fun i _ => S.smul_mem _ (hmem i)⟩ : S)) ?_
  intro y
  obtain ⟨c, hc⟩ := hspan y y.2
  refine ⟨fun i => Ideal.Quotient.mk (maximalIdeal Λ ^ (n + 1)) (c i), Subtype.ext ?_⟩
  show ∑ i, s (Ideal.Quotient.mk (maximalIdeal Λ ^ (n + 1)) (c i)) • (i : B) = y
  rw [← hc, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← sub_smul]
  exact hn' _ (Ideal.Quotient.eq.mp (hs _)) i

/- English proof (translation)
Establish `hT : ∀ n k, ∃ T : M (n + k) ⟶ M n, (∀ c, T.hom (p (n + k) c) = p n c) ∧ (F.map T).hom (ξ (n + k)) = ξ n`. Introduce `n k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨𝟙 _, fun c => rfl, by rw [F.map_id]; rfl⟩`. Consider the case `succ k ih`.

Take `⟨T, hT1, hT2⟩` from `ih`. Conclude with `⟨t (n + k) ≫ T, fun c => (congrArg T.hom (hpt (n + k) c)).trans (hT1 c), by rw [F.map_comp]; exact (congrArg (F.map T).hom (ht (n + k))).trans hT2⟩`. Establish `hup : ∀ (B : ModuleCat.{0} Λ) (x : Fin a → B) (y : F.obj B) (n m : ℕ), n ≤ m → (∃ φ : M n ⟶ B, (∀ c, φ.hom (p n c) = ∑ i, c i • x i) ∧ (F.map φ).hom (ξ n) = y) → ∃ φ : M m ⟶ B, (∀ c, φ.hom (p m c) = ∑ i, c i • x i) ∧ (F.map φ).hom (ξ m) = y`. Introduce and unpack `B x y n m hnm ⟨φ, h1, h2⟩`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hnm`.

Take `⟨T, hT1, hT2⟩` from `hT n k`. Use `⟨T ≫ φ, fun c => (congrArg φ.hom (hT1 c)).trans (h1 c), ?_⟩` and prove the remaining obligations. Rewrite using `[F.map_comp]`. Conclude with `(congrArg (F.map φ).hom hT2).trans h2`. Establish `hext : ∀ (B : ModuleCat.{0} Λ) (n : ℕ) (φ ψ : M n ⟶ B), (∀ c, φ.hom (p n c) = ψ.hom (p n c)) → φ = ψ`.

Introduce `B n φ ψ h`. Use extensionality with `m`. Take `⟨c, rfl⟩` from `hp n m`. Conclude with `h c`. Establish `hmin' : ∀ (B : ModuleCat.{0} Λ), Tors Λ B → ∀ (n : ℕ) (φ ψ : M n ⟶ B), (F.map φ).hom (ξ n) = (F.map ψ).hom (ξ n) → φ = ψ`.

Introduce `B hB n φ ψ h`. Use `hmin n B hB (φ - ψ) (by rw [F.map_sub, ModuleCat.hom_sub, LinearMap.sub_apply, h, sub_self])` as an intermediate fact. Conclude with `sub_eq_zero.mp this`. Establish `hcoord : ∀ (B : ModuleCat.{0} Λ) (x : Fin a → B) (i : Fin a), ∑ j, (Pi.single i (1 : Λ) : Fin a → Λ) j • x j = x i`. Introduce `B x i`.

Simplify using `[Pi.single_apply]`. Establish `key : ∀ (B : ModuleCat.{0} Λ) (hB : Tors Λ B), ∃ e : ↥(sol N B) ≃ₗ[Λ] F.obj B, ∀ x : sol N B, ∃ n, ∃ φ : M n ⟶ B, (∀ c, φ.hom (p n c) = ∑ i, c i • x.1 i) ∧ (F.map φ).hom (ξ n) = e x`. Introduce `B hB`. Use `exists_equiv_of_rel (fun (x : sol N B) (y : F.obj B) => ∃ n, ∃ φ : M n ⟶ B, (∀ c, φ.hom (p n c) = ∑ i, c i • x.1 i) ∧ (F.map φ).hom (ξ n) = y) ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x`.

Take `⟨n, hn⟩` from `exists_pow_kill hB x.1`. Take `⟨L, hL⟩ : ∃ L : (Fin a → Λ) →ₗ[Λ] B, ∀ c, L c = ∑ i, c i • x.1 i` from `⟨{ toFun := fun c => ∑ i, c i • x.1 i map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] map_smul' := fun r c => by simp [Finset.smul_sum, mul_smul] }, fun _ => rfl⟩`. Establish `hker : LinearMap.ker (p n) ≤ LinearMap.ker L`. Introduce `c hc`. Take `⟨c1, hc1, c2, hc2, rfl⟩` from `Submodule.mem_sup.mp (hN' n hc)`.

Establish `hsm : maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) ≤ LinearMap.ker L`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr d _`. Rewrite using `[LinearMap.mem_ker, hL]`. Conclude with `Finset.sum_eq_zero fun i _ => by`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, mul_comm, mul_smul, hn r hr i, smul_zero]`. Establish `h2 : L c2 = 0` using `hsm hc2`. Rewrite using `[LinearMap.mem_ker, map_add, h2, add_zero, hL]`. Conclude with `(mem_sol.mp x.2) c1 hc1`. Use `⟨_, n, ModuleCat.ofHom ((LinearMap.ker (p n)).liftQ L hker ∘ₗ (LinearMap.quotKerEquivOfSurjective (p n) (hp n)).symm.toLinearMap), fun c => ?_, rfl⟩` and prove the remaining obligations.

Establish `hs : (LinearMap.quotKerEquivOfSurjective (p n) (hp n)).symm (p n c) = Submodule.Quotient.mk c`. Rewrite using `[LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]`. Use `show (LinearMap.ker (p n)).liftQ L hker ((LinearMap.quotKerEquivOfSurjective (p n) (hp n)).symm (p n c)) = _`. Rewrite using `[hs, Submodule.liftQ_apply, hL]`. Introduce and unpack `x y y' ⟨n, φ, h1, h2⟩ ⟨n', φ', h1', h2'⟩`.

Take `⟨ψ, g1, g2⟩` from `hup B x.1 y n (max n n') (le_max_left _ _) ⟨φ, h1, h2⟩`. Take `⟨ψ', g1', g2'⟩` from `hup B x.1 y' n' (max n n') (le_max_right _ _) ⟨φ', h1', h2'⟩`. Establish `: ψ = ψ'` using `hext B _ ψ ψ' fun c => (g1 c).trans (g1' c).symm`. Rewrite using `[← g2, ← g2', this]`. Introduce and unpack `x x' y ⟨n, φ, h1, h2⟩ ⟨n', φ', h1', h2'⟩`.

Take `⟨ψ, g1, g2⟩` from `hup B x.1 y n (max n n') (le_max_left _ _) ⟨φ, h1, h2⟩`. Take `⟨ψ', g1', g2'⟩` from `hup B x'.1 y n' (max n n') (le_max_right _ _) ⟨φ', h1', h2'⟩`. Establish `: ψ = ψ'` using `hmin' B hB _ ψ ψ' (g2.trans g2'.symm)`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Rewrite using `[← hcoord B x.1 i, ← hcoord B x'.1 i, ← g1, ← g1', this]`. Introduce `y`. Take `⟨S, hS, hy⟩` from `hcol B hB y`. Take `⟨z, rfl⟩` from `hy`. Take `⟨hfin, n, hn⟩` from `fg_finite hB S hS`.

Take `⟨φ, hφ⟩` from `huniv n (ModuleCat.of Λ S) hfin (fun r hr w => hn r hr w) z`. Establish `hx : (fun i => (φ ≫ ModuleCat.ofHom S.subtype).hom (p n (Pi.single i 1))) ∈ sol N B`. Rewrite using `[mem_sol]`. Introduce `c hc`. Establish `h1` using `lin_eq_sum ((φ ≫ ModuleCat.ofHom S.subtype).hom ∘ₗ p n) c`.

Rewrite `h1` using `[LinearMap.comp_apply, LinearMap.mem_ker.mp (hN n hc), map_zero]`. Conclude with `h1.symm`. Use `⟨⟨_, hx⟩, n, φ ≫ ModuleCat.ofHom S.subtype, fun c => ?_, ?_⟩` and prove the remaining obligations. Conclude with `lin_eq_sum ((φ ≫ ModuleCat.ofHom S.subtype).hom ∘ₗ p n) c`. Rewrite using `[F.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hφ]`.

Introduce and unpack `x x' y y' ⟨n, φ, h1, h2⟩ ⟨n', φ', h1', h2'⟩`. Take `⟨ψ, g1, g2⟩` from `hup B x.1 y n (max n n') (le_max_left _ _) ⟨φ, h1, h2⟩`. Take `⟨ψ', g1', g2'⟩` from `hup B x'.1 y' n' (max n n') (le_max_right _ _) ⟨φ', h1', h2'⟩`. Use `⟨max n n', ψ + ψ', fun c => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ModuleCat.hom_add, LinearMap.add_apply, g1, g1', ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun i _ => (smul_add _ _ _).symm`. Rewrite using `[F.map_add, ModuleCat.hom_add, LinearMap.add_apply, g2, g2']`. Introduce and unpack `r x y ⟨n, φ, h1, h2⟩`. Use `⟨n, r • φ, fun c => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ModuleCat.hom_smul, LinearMap.smul_apply, h1, Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => smul_comm r (c i) (x.1 i)`. Rewrite using `[F.map_smul, ModuleCat.hom_smul, LinearMap.smul_apply, h2]`. Use `choose e he using key`. Use `⟨e, fun B B' hB hB' f x x' hx => ?_⟩` and prove the remaining obligations. Take `⟨n, φ, h1, h2⟩` from `he B hB x`.

Take `⟨n', φ', h1', h2'⟩` from `he B' hB' x'`. Establish `w1 : ∀ c, (φ ≫ f).hom (p n c) = ∑ i, c i • x'.1 i`. Introduce `c`. Use `show f.hom (φ.hom (p n c)) = _`. Rewrite using `[h1, map_sum]`.

Simplify using `only [map_smul, hx]`. Establish `w2 : (F.map (φ ≫ f)).hom (ξ n) = (F.map f).hom (e B hB x)`. Rewrite using `[F.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, h2]`. Take `⟨ψ, g1, g2⟩` from `hup B' x'.1 ((F.map f).hom (e B hB x)) n (max n n') (le_max_left _ _) ⟨φ ≫ f, w1, w2⟩`. Take `⟨ψ', g1', g2'⟩` from `hup B' x'.1 (e B' hB' x') n' (max n n') (le_max_right _ _) ⟨φ', h1', h2'⟩`.

Establish `: ψ = ψ'` using `hext B' _ ψ ψ' fun c => (g1 c).trans (g1' c).symm`. Rewrite using `[← g2', ← this, g2]`.
-/
theorem assemble [IsNoetherianRing Λ] [Finite (ResidueField Λ)] (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive]
    [F.Linear Λ]
    (hcol : ∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ y : F.obj B, ∃ B' : Submodule Λ B, B'.FG ∧
      y ∈ LinearMap.range (F.map (ModuleCat.ofHom B'.subtype)).hom)
    (M : ℕ → ModuleCat.{0} Λ) (ξ : ∀ n, F.obj (M n)) (t : ∀ n, M (n + 1) ⟶ M n)
    (ht : ∀ n, (F.map (t n)).hom (ξ (n + 1)) = ξ n)
    (hmin : ∀ n, ∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ φ : M n ⟶ B, (F.map φ).hom (ξ n) = 0 → φ = 0)
    (huniv : ∀ n, ∀ B : ModuleCat.{0} Λ, Finite B → (∀ x ∈ maximalIdeal Λ ^ (n + 1), ∀ y : B, x • y = 0) →
      ∀ η : F.obj B, ∃ φ : M n ⟶ B, (F.map φ).hom (ξ n) = η)
    {a : ℕ} (p : ∀ n, (Fin a → Λ) →ₗ[Λ] M n) (hp : ∀ n, Function.Surjective (p n))
    (hpt : ∀ n c, (t n).hom (p (n + 1) c) = p n c) (N : Submodule Λ (Fin a → Λ)) (hN : ∀ n, N ≤ LinearMap.ker (p n))
    (hN' : ∀ n, LinearMap.ker (p n) ≤ N ⊔ maximalIdeal Λ ^ (n + 1) • ⊤) :
    ∃ e : ∀ B : ModuleCat.{0} Λ, Tors Λ B → (↥(sol N B) ≃ₗ[Λ] F.obj B),
      ∀ (B B' : ModuleCat.{0} Λ) (hB : Tors Λ B) (hB' : Tors Λ B') (f : B ⟶ B') (x : sol N B) (x' : sol N B'),
        (∀ c, x'.1 c = f.hom (x.1 c)) → e B' hB' x' = (F.map f).hom (e B hB x) := by
  classical
  have hT : ∀ n k, ∃ T : M (n + k) ⟶ M n, (∀ c, T.hom (p (n + k) c) = p n c) ∧
      (F.map T).hom (ξ (n + k)) = ξ n := by
    intro n k
    induction k with
    | zero => exact ⟨𝟙 _, fun c => rfl, by rw [F.map_id]; rfl⟩
    | succ k ih =>
      obtain ⟨T, hT1, hT2⟩ := ih
      exact ⟨t (n + k) ≫ T, fun c => (congrArg T.hom (hpt (n + k) c)).trans (hT1 c),
        by rw [F.map_comp]; exact (congrArg (F.map T).hom (ht (n + k))).trans hT2⟩
  have hup : ∀ (B : ModuleCat.{0} Λ) (x : Fin a → B) (y : F.obj B) (n m : ℕ), n ≤ m →
      (∃ φ : M n ⟶ B, (∀ c, φ.hom (p n c) = ∑ i, c i • x i) ∧ (F.map φ).hom (ξ n) = y) →
      ∃ φ : M m ⟶ B, (∀ c, φ.hom (p m c) = ∑ i, c i • x i) ∧ (F.map φ).hom (ξ m) = y := by
    rintro B x y n m hnm ⟨φ, h1, h2⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    obtain ⟨T, hT1, hT2⟩ := hT n k
    refine ⟨T ≫ φ, fun c => (congrArg φ.hom (hT1 c)).trans (h1 c), ?_⟩
    rw [F.map_comp]
    exact (congrArg (F.map φ).hom hT2).trans h2
  have hext : ∀ (B : ModuleCat.{0} Λ) (n : ℕ) (φ ψ : M n ⟶ B),
      (∀ c, φ.hom (p n c) = ψ.hom (p n c)) → φ = ψ := by
    intro B n φ ψ h
    ext m
    obtain ⟨c, rfl⟩ := hp n m
    exact h c
  have hmin' : ∀ (B : ModuleCat.{0} Λ), Tors Λ B → ∀ (n : ℕ) (φ ψ : M n ⟶ B),
      (F.map φ).hom (ξ n) = (F.map ψ).hom (ξ n) → φ = ψ := by
    intro B hB n φ ψ h
    have := hmin n B hB (φ - ψ) (by rw [F.map_sub, ModuleCat.hom_sub, LinearMap.sub_apply, h, sub_self])
    exact sub_eq_zero.mp this
  have hcoord : ∀ (B : ModuleCat.{0} Λ) (x : Fin a → B) (i : Fin a),
      ∑ j, (Pi.single i (1 : Λ) : Fin a → Λ) j • x j = x i := by
    intro B x i
    simp [Pi.single_apply]
  have key : ∀ (B : ModuleCat.{0} Λ) (hB : Tors Λ B), ∃ e : ↥(sol N B) ≃ₗ[Λ] F.obj B, ∀ x : sol N B,
      ∃ n, ∃ φ : M n ⟶ B, (∀ c, φ.hom (p n c) = ∑ i, c i • x.1 i) ∧ (F.map φ).hom (ξ n) = e x := by
    intro B hB
    refine exists_equiv_of_rel (fun (x : sol N B) (y : F.obj B) => ∃ n, ∃ φ : M n ⟶ B,
      (∀ c, φ.hom (p n c) = ∑ i, c i • x.1 i) ∧ (F.map φ).hom (ξ n) = y) ?_ ?_ ?_ ?_ ?_ ?_
    · intro x
      obtain ⟨n, hn⟩ := exists_pow_kill hB x.1
      obtain ⟨L, hL⟩ : ∃ L : (Fin a → Λ) →ₗ[Λ] B, ∀ c, L c = ∑ i, c i • x.1 i :=
        ⟨{ toFun := fun c => ∑ i, c i • x.1 i
           map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
           map_smul' := fun r c => by simp [Finset.smul_sum, mul_smul] }, fun _ => rfl⟩
      have hker : LinearMap.ker (p n) ≤ LinearMap.ker L := by
        intro c hc
        obtain ⟨c1, hc1, c2, hc2, rfl⟩ := Submodule.mem_sup.mp (hN' n hc)
        have hsm : maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) ≤ LinearMap.ker L := by
          rw [Submodule.smul_le]
          intro r hr d _
          rw [LinearMap.mem_ker, hL]
          exact Finset.sum_eq_zero fun i _ => by
            rw [Pi.smul_apply, smul_eq_mul, mul_comm, mul_smul, hn r hr i, smul_zero]
        have h2 : L c2 = 0 := hsm hc2
        rw [LinearMap.mem_ker, map_add, h2, add_zero, hL]
        exact (mem_sol.mp x.2) c1 hc1
      refine ⟨_, n, ModuleCat.ofHom ((LinearMap.ker (p n)).liftQ L hker ∘ₗ
        (LinearMap.quotKerEquivOfSurjective (p n) (hp n)).symm.toLinearMap), fun c => ?_, rfl⟩
      have hs : (LinearMap.quotKerEquivOfSurjective (p n) (hp n)).symm (p n c) = Submodule.Quotient.mk c := by
        rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
      show (LinearMap.ker (p n)).liftQ L hker ((LinearMap.quotKerEquivOfSurjective (p n) (hp n)).symm (p n c)) = _
      rw [hs, Submodule.liftQ_apply, hL]
    · rintro x y y' ⟨n, φ, h1, h2⟩ ⟨n', φ', h1', h2'⟩
      obtain ⟨ψ, g1, g2⟩ := hup B x.1 y n (max n n') (le_max_left _ _) ⟨φ, h1, h2⟩
      obtain ⟨ψ', g1', g2'⟩ := hup B x.1 y' n' (max n n') (le_max_right _ _) ⟨φ', h1', h2'⟩
      have : ψ = ψ' := hext B _ ψ ψ' fun c => (g1 c).trans (g1' c).symm
      rw [← g2, ← g2', this]
    · rintro x x' y ⟨n, φ, h1, h2⟩ ⟨n', φ', h1', h2'⟩
      obtain ⟨ψ, g1, g2⟩ := hup B x.1 y n (max n n') (le_max_left _ _) ⟨φ, h1, h2⟩
      obtain ⟨ψ', g1', g2'⟩ := hup B x'.1 y n' (max n n') (le_max_right _ _) ⟨φ', h1', h2'⟩
      have : ψ = ψ' := hmin' B hB _ ψ ψ' (g2.trans g2'.symm)
      apply Subtype.ext
      funext i
      rw [← hcoord B x.1 i, ← hcoord B x'.1 i, ← g1, ← g1', this]
    · intro y
      obtain ⟨S, hS, hy⟩ := hcol B hB y
      obtain ⟨z, rfl⟩ := hy
      obtain ⟨hfin, n, hn⟩ := fg_finite hB S hS
      obtain ⟨φ, hφ⟩ := huniv n (ModuleCat.of Λ S) hfin (fun r hr w => hn r hr w) z
      have hx : (fun i => (φ ≫ ModuleCat.ofHom S.subtype).hom (p n (Pi.single i 1))) ∈ sol N B := by
        rw [mem_sol]
        intro c hc
        have h1 := lin_eq_sum ((φ ≫ ModuleCat.ofHom S.subtype).hom ∘ₗ p n) c
        rw [LinearMap.comp_apply, LinearMap.mem_ker.mp (hN n hc), map_zero] at h1
        exact h1.symm
      refine ⟨⟨_, hx⟩, n, φ ≫ ModuleCat.ofHom S.subtype, fun c => ?_, ?_⟩
      · exact lin_eq_sum ((φ ≫ ModuleCat.ofHom S.subtype).hom ∘ₗ p n) c
      · rw [F.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hφ]
    · rintro x x' y y' ⟨n, φ, h1, h2⟩ ⟨n', φ', h1', h2'⟩
      obtain ⟨ψ, g1, g2⟩ := hup B x.1 y n (max n n') (le_max_left _ _) ⟨φ, h1, h2⟩
      obtain ⟨ψ', g1', g2'⟩ := hup B x'.1 y' n' (max n n') (le_max_right _ _) ⟨φ', h1', h2'⟩
      refine ⟨max n n', ψ + ψ', fun c => ?_, ?_⟩
      · rw [ModuleCat.hom_add, LinearMap.add_apply, g1, g1', ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => (smul_add _ _ _).symm
      · rw [F.map_add, ModuleCat.hom_add, LinearMap.add_apply, g2, g2']
    · rintro r x y ⟨n, φ, h1, h2⟩
      refine ⟨n, r • φ, fun c => ?_, ?_⟩
      · rw [ModuleCat.hom_smul, LinearMap.smul_apply, h1, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_comm r (c i) (x.1 i)
      · rw [F.map_smul, ModuleCat.hom_smul, LinearMap.smul_apply, h2]
  choose e he using key
  refine ⟨e, fun B B' hB hB' f x x' hx => ?_⟩
  obtain ⟨n, φ, h1, h2⟩ := he B hB x
  obtain ⟨n', φ', h1', h2'⟩ := he B' hB' x'
  have w1 : ∀ c, (φ ≫ f).hom (p n c) = ∑ i, c i • x'.1 i := by
    intro c
    show f.hom (φ.hom (p n c)) = _
    rw [h1, map_sum]
    simp only [map_smul, hx]
  have w2 : (F.map (φ ≫ f)).hom (ξ n) = (F.map f).hom (e B hB x) := by
    rw [F.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, h2]
  obtain ⟨ψ, g1, g2⟩ := hup B' x'.1 ((F.map f).hom (e B hB x)) n (max n n') (le_max_left _ _) ⟨φ ≫ f, w1, w2⟩
  obtain ⟨ψ', g1', g2'⟩ := hup B' x'.1 (e B' hB' x') n' (max n n') (le_max_right _ _) ⟨φ', h1', h2'⟩
  have : ψ = ψ' := hext B' _ ψ ψ' fun c => (g1 c).trans (g1' c).symm
  rw [← g2', ← this, g2]

/- English proof (translation)
Take `⟨B, f, hBt, hf, hext⟩` from `GlobalTheory.T.exists_torsion_module_extending_residue_maps Λ (Fin a → Λ) N`. Set `K : ModuleCat.{0} Λ` to `ModuleCat.of Λ (ResidueField Λ)`. Set `B'' : ModuleCat.{0} Λ` to `ModuleCat.of Λ (B ⧸ LinearMap.range f)`. Set `fK : K ⟶ B` to `ModuleCat.ofHom f`. Set `g : B ⟶ B''` to `ModuleCat.ofHom (LinearMap.range f).mkQ`.

Establish `hB'' : Tors Λ B''`. Introduce `y`. Take `⟨z, rfl⟩` from `Submodule.mkQ_surjective _ y`. Take `⟨n, hn⟩` from `hBt z`. Use `⟨n, fun r hr => ?_⟩` and prove the remaining obligations.

Use `show r • Submodule.Quotient.mk (p := LinearMap.range f) z = 0`. Rewrite using `[← Submodule.Quotient.mk_smul, hn r hr, Submodule.Quotient.mk_zero]`. Establish `hex : Function.Exact fK.hom g.hom` using `LinearMap.exact_map_mkQ_range f`. Take `⟨_, hfinQ, hcard⟩` from `hobs K B B'' hK hBt fK g hf hex (Submodule.mkQ_surjective _)`. Use `choose u hu using hext`.

Establish `hsolB'' : ∀ φ : N →ₗ[Λ] ResidueField Λ, (fun i => g.hom (u φ (Pi.single i 1))) ∈ sol N B''`. Introduce `φ`. Rewrite using `[mem_sol]`. Introduce `c hc`. Use `show ∑ i, c i • g.hom (u φ (Pi.single i 1)) = 0`.

Establish `h1` using `lin_eq_sum (g.hom ∘ₗ u φ) c`. Establish `h2` using `LinearMap.congr_fun (hu φ) ⟨c, hc⟩`. Establish `h3 : u φ c = f (φ ⟨c, hc⟩)` using `h2`. Establish `h4 : g.hom (f (φ ⟨c, hc⟩)) = 0` using `hex.apply_apply_eq_zero _`. Rewrite `h1` using `[LinearMap.comp_apply, h3, h4]`.

Conclude with `h1.symm`. Set `Ψ : (N →ₗ[Λ] ResidueField Λ) → F.obj B'' ⧸ LinearMap.range (F.map g).hom` to `fun φ => Submodule.Quotient.mk (e B'' hB'' ⟨_, hsolB'' φ⟩)`. Establish `hΨ : Function.Injective Ψ`. Introduce `φ φ' h`. Establish `h'` using `(Submodule.Quotient.eq _).mp h`.

Rewrite `h'` using `[← map_sub]`. Take `⟨w, hw⟩` from `h'`. Set `y` to `(e B hBt).symm w`. Establish `hy : ∀ c ∈ N, ∑ i, c i • y.1 i = 0` using `mem_sol.mp y.2`. Establish `hgy : (fun i => g.hom (y.1 i)) ∈ sol N B''`.

Rewrite using `[mem_sol]`. Introduce `c hc`. Establish `: ∑ i, c i • g.hom (y.1 i) = g.hom (∑ i, c i • y.1 i)` using `by simp [map_sum, map_smul]`. Rewrite using `[this, hy c hc, map_zero]`. Establish `hnat` using `he B B'' hBt hB'' g y ⟨_, hgy⟩ (fun c => rfl)`.

Establish `hEq : (⟨_, hgy⟩ : sol N B'') = ⟨_, hsolB'' φ⟩ - ⟨_, hsolB'' φ'⟩`. Apply `(e B'' hB'').injective` to reduce the goal to its premises. Rewrite using `[hnat, LinearEquiv.apply_symm_apply, hw]`. Establish `hz : ∀ i, ∃ z : ResidueField Λ, f z = u φ (Pi.single i 1) - u φ' (Pi.single i 1) - y.1 i`. Introduce `i`.

Establish `hi : g.hom (y.1 i) = g.hom (u φ (Pi.single i 1)) - g.hom (u φ' (Pi.single i 1))` using `congrArg (fun s : sol N B'' => s.1 i) hEq`. Establish `h0 : g.hom (u φ (Pi.single i 1) - u φ' (Pi.single i 1) - y.1 i) = 0`. Rewrite using `[map_sub, map_sub, hi, sub_self]`. Conclude with `(hex _).mp h0`. Use `choose z hz using hz`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce and unpack `⟨c, hc⟩`. Apply `hf` to reduce the goal to its premises. Establish `e1 : ∀ ψ : N →ₗ[Λ] ResidueField Λ, f (ψ ⟨c, hc⟩) = ∑ i, c i • u ψ (Pi.single i 1)`. Introduce `ψ`.

Rewrite using `[← lin_eq_sum]`. Conclude with `(LinearMap.congr_fun (hu ψ) ⟨c, hc⟩).symm`. Establish `e2 : ∑ i, c i • f (z i) = 0` using `Finset.sum_eq_zero fun i _ => by rw [← map_smul, hKm _ (hN c hc i), map_zero]`. Establish `e3 : ∀ i, u φ (Pi.single i 1) = f (z i) + u φ' (Pi.single i 1) + y.1 i` using `fun i => by`. Rewrite using `[hz i]`.

Normalize the expressions using the abelian group laws. Use `show f (φ ⟨c, hc⟩) = f (φ' ⟨c, hc⟩)`. Rewrite using `[e1 φ, e1 φ']`. Simplify using `only [e3, smul_add, Finset.sum_add_distrib, e2, hy c hc, zero_add, add_zero]`. Establish `hle1 : Nat.card (N →ₗ[Λ] ResidueField Λ) ≤ Nat.card (F.obj B'' ⧸ LinearMap.range (F.map g).hom)`.

Use `hfinQ` as an intermediate fact. Conclude with `Nat.card_le_card_of_injective Ψ hΨ`. Establish `hKt : Tors Λ K` using `fun y => ⟨1, fun r hr => by rw [pow_one] at hr; exact hKm r hr y⟩`. Establish `hle2 : Nat.card (F.obj K) ≤ Nat.card (ResidueField Λ) ^ a`. Rewrite using `[← Nat.card_congr (e K hKt).toEquiv]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a), Fintype.card_fin]`. Conclude with `GlobalTheory.T.exists_generators_of_card_hom_residueField_le Λ N a (hle1.trans (hcard.trans hle2))`.
-/
theorem few_relations [IsNoetherianRing Λ] [Finite (ResidueField Λ)] (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ)
    (hobs : ∀ (K B B'' : ModuleCat.{0} Λ), IsSimpleModule Λ K → Tors Λ B → ∀ (f : K ⟶ B) (g : B ⟶ B''),
      Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
      Finite (F.obj K) ∧ Finite (F.obj B'' ⧸ LinearMap.range (F.map g).hom) ∧
        Nat.card (F.obj B'' ⧸ LinearMap.range (F.map g).hom) ≤ Nat.card (F.obj K))
    (hK : IsSimpleModule Λ (ResidueField Λ)) (hKm : ∀ r ∈ maximalIdeal Λ, ∀ y : ResidueField Λ, r • y = 0)
    {a : ℕ} (N : Submodule Λ (Fin a → Λ)) (hN : ∀ c ∈ N, ∀ i, c i ∈ maximalIdeal Λ)
    (e : ∀ B : ModuleCat.{0} Λ, Tors Λ B → (↥(sol N B) ≃ₗ[Λ] F.obj B))
    (he : ∀ (B B' : ModuleCat.{0} Λ) (hB : Tors Λ B) (hB' : Tors Λ B') (f : B ⟶ B') (x : sol N B) (x' : sol N B'),
        (∀ c, x'.1 c = f.hom (x.1 c)) → e B' hB' x' = (F.map f).hom (e B hB x)) :
    ∃ v : Fin a → N, Submodule.span Λ (Set.range v) = ⊤ := by
  classical
  obtain ⟨B, f, hBt, hf, hext⟩ := GlobalTheory.T.exists_torsion_module_extending_residue_maps Λ (Fin a → Λ) N
  let K : ModuleCat.{0} Λ := ModuleCat.of Λ (ResidueField Λ)
  let B'' : ModuleCat.{0} Λ := ModuleCat.of Λ (B ⧸ LinearMap.range f)
  let fK : K ⟶ B := ModuleCat.ofHom f
  let g : B ⟶ B'' := ModuleCat.ofHom (LinearMap.range f).mkQ
  have hB'' : Tors Λ B'' := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨n, hn⟩ := hBt z
    refine ⟨n, fun r hr => ?_⟩
    show r • Submodule.Quotient.mk (p := LinearMap.range f) z = 0
    rw [← Submodule.Quotient.mk_smul, hn r hr, Submodule.Quotient.mk_zero]
  have hex : Function.Exact fK.hom g.hom := LinearMap.exact_map_mkQ_range f
  obtain ⟨_, hfinQ, hcard⟩ := hobs K B B'' hK hBt fK g hf hex (Submodule.mkQ_surjective _)
  choose u hu using hext
  have hsolB'' : ∀ φ : N →ₗ[Λ] ResidueField Λ, (fun i => g.hom (u φ (Pi.single i 1))) ∈ sol N B'' := by
    intro φ
    rw [mem_sol]
    intro c hc
    show ∑ i, c i • g.hom (u φ (Pi.single i 1)) = 0
    have h1 := lin_eq_sum (g.hom ∘ₗ u φ) c
    have h2 := LinearMap.congr_fun (hu φ) ⟨c, hc⟩
    have h3 : u φ c = f (φ ⟨c, hc⟩) := h2
    have h4 : g.hom (f (φ ⟨c, hc⟩)) = 0 := hex.apply_apply_eq_zero _
    rw [LinearMap.comp_apply, h3, h4] at h1
    exact h1.symm
  let Ψ : (N →ₗ[Λ] ResidueField Λ) → F.obj B'' ⧸ LinearMap.range (F.map g).hom :=
    fun φ => Submodule.Quotient.mk (e B'' hB'' ⟨_, hsolB'' φ⟩)
  have hΨ : Function.Injective Ψ := by
    intro φ φ' h
    have h' := (Submodule.Quotient.eq _).mp h
    rw [← map_sub] at h'
    obtain ⟨w, hw⟩ := h'
    let y := (e B hBt).symm w
    have hy : ∀ c ∈ N, ∑ i, c i • y.1 i = 0 := mem_sol.mp y.2
    have hgy : (fun i => g.hom (y.1 i)) ∈ sol N B'' := by
      rw [mem_sol]
      intro c hc
      have : ∑ i, c i • g.hom (y.1 i) = g.hom (∑ i, c i • y.1 i) := by simp [map_sum, map_smul]
      rw [this, hy c hc, map_zero]
    have hnat := he B B'' hBt hB'' g y ⟨_, hgy⟩ (fun c => rfl)
    have hEq : (⟨_, hgy⟩ : sol N B'') = ⟨_, hsolB'' φ⟩ - ⟨_, hsolB'' φ'⟩ := by
      apply (e B'' hB'').injective
      rw [hnat, LinearEquiv.apply_symm_apply, hw]
    have hz : ∀ i, ∃ z : ResidueField Λ, f z = u φ (Pi.single i 1) - u φ' (Pi.single i 1) - y.1 i := by
      intro i
      have hi : g.hom (y.1 i) = g.hom (u φ (Pi.single i 1)) - g.hom (u φ' (Pi.single i 1)) :=
        congrArg (fun s : sol N B'' => s.1 i) hEq
      have h0 : g.hom (u φ (Pi.single i 1) - u φ' (Pi.single i 1) - y.1 i) = 0 := by
        rw [map_sub, map_sub, hi, sub_self]
      exact (hex _).mp h0
    choose z hz using hz
    apply LinearMap.ext
    rintro ⟨c, hc⟩
    apply hf
    have e1 : ∀ ψ : N →ₗ[Λ] ResidueField Λ, f (ψ ⟨c, hc⟩) = ∑ i, c i • u ψ (Pi.single i 1) := by
      intro ψ
      rw [← lin_eq_sum]
      exact (LinearMap.congr_fun (hu ψ) ⟨c, hc⟩).symm
    have e2 : ∑ i, c i • f (z i) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [← map_smul, hKm _ (hN c hc i), map_zero]
    have e3 : ∀ i, u φ (Pi.single i 1) = f (z i) + u φ' (Pi.single i 1) + y.1 i := fun i => by
      rw [hz i]; abel
    show f (φ ⟨c, hc⟩) = f (φ' ⟨c, hc⟩)
    rw [e1 φ, e1 φ']
    simp only [e3, smul_add, Finset.sum_add_distrib, e2, hy c hc, zero_add, add_zero]
  have hle1 : Nat.card (N →ₗ[Λ] ResidueField Λ) ≤ Nat.card (F.obj B'' ⧸ LinearMap.range (F.map g).hom) := by
    have := hfinQ
    exact Nat.card_le_card_of_injective Ψ hΨ
  have hKt : Tors Λ K := fun y => ⟨1, fun r hr => by rw [pow_one] at hr; exact hKm r hr y⟩
  have hle2 : Nat.card (F.obj K) ≤ Nat.card (ResidueField Λ) ^ a := by
    rw [← Nat.card_congr (e K hKt).toEquiv]
    calc Nat.card (sol N K) ≤ Nat.card (Fin a → ResidueField Λ) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = Nat.card (ResidueField Λ) ^ a := by
          rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a), Fintype.card_fin]
  exact GlobalTheory.T.exists_generators_of_card_hom_residueField_le Λ N a (hle1.trans (hcard.trans hle2))

/- English proof (translation)
Introduce `r hr y`. Rewrite using `[Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff r).mpr hr, zero_mul]`.
-/
theorem residue_kill : ∀ r ∈ maximalIdeal Λ, ∀ y : ResidueField Λ, r • y = 0 := by
  intro r hr y
  rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
    (IsLocalRing.residue_eq_zero_iff r).mpr hr, zero_mul]

/- English proof (translation)
The claim follows from `isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal Λ).out`.
-/
theorem residue_simple : IsSimpleModule Λ (ResidueField Λ) :=
  isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal Λ).out

/- English proof (translation)
Unfold `KernelRep`. Introduce `Λ _ _ _ _ _ F _ _ hlex hcol hobs`. Establish `hres` using `residue_kill (Λ := Λ)`. Establish `hsimple` using `residue_simple (Λ := Λ)`. Establish `htors : ∀ (B : ModuleCat.{0} Λ) (n : ℕ), (∀ x ∈ maximalIdeal Λ ^ n, ∀ y : B, x • y = 0) → Tors Λ B` using `fun B n h y => ⟨n, fun x hx => h x hx y⟩`.

Establish `hFk : Finite (F.obj (ModuleCat.of Λ (ResidueField Λ)))`. Establish `hKt : Tors Λ (ModuleCat.of Λ (ResidueField Λ))` using `htors _ 1 (fun r hr y => by rw [pow_one] at hr; exact hres r hr y)`. Conclude with `(hobs (ModuleCat.of Λ (ResidueField Λ)) (ModuleCat.of Λ (ResidueField Λ)) (ModuleCat.of Λ PUnit.{1}) hsimple hKt (𝟙 _) 0 (fun _ _ h => h) (fun y => ⟨fun _ => ⟨y, rfl⟩, fun _ => rfl⟩) (fun _ => ⟨0, rfl⟩)).1`. Use `choose M0 ξ0 hfin hkill hmin0 huniv0 using GlobalTheory.T.leftExact_functor_representable_torsion_modules Λ F hlex hFk`. Establish `: ∀ n, Finite (M0 n)` using `hfin`.

Establish `htr : ∀ n, ∃ t : M0 (n + 1 + 1) ⟶ M0 (n + 1), (F.map t).hom (ξ0 (n + 1 + 1)) = ξ0 (n + 1)` using `fun n => huniv0 (n + 1 + 1) (M0 (n + 1)) (hfin (n + 1)) (fun x hx y => hkill (n + 1) x (Ideal.pow_le_pow_right (Nat.le_succ _) hx) y) (ξ0 (n + 1))`. Use `choose t ht using htr`. Establish `hkerT : ∀ n, LinearMap.ker (t n).hom ≤ maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (M0 (n + 1 + 1)))`. Introduce `n`. Set `Q : ModuleCat.{0} Λ` to `ModuleCat.of Λ (M0 (n + 1 + 1) ⧸ maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (M0 (n + 1 + 1))))`.

Set `q : M0 (n + 1 + 1) ⟶ Q` to `ModuleCat.ofHom (Submodule.mkQ _)`. Establish `hQkill : ∀ x ∈ maximalIdeal Λ ^ (n + 1), ∀ y : Q, x • y = 0`. Introduce `x hx y`. Take `⟨z, rfl⟩` from `Submodule.mkQ_surjective _ y`. Rewrite using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `Submodule.smul_mem_smul hx Submodule.mem_top`. Establish `hQfin : Finite Q` using `Finite.of_surjective _ (Submodule.mkQ_surjective (maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (M0 (n + 1 + 1)))))`. Take `⟨ψ, hψ⟩` from `huniv0 (n + 1) Q hQfin hQkill ((F.map q).hom (ξ0 (n + 1 + 1)))`. Establish `heq : t n ≫ ψ = q`. Use `hmin0 (n + 1 + 1) Q (htors Q _ hQkill) (t n ≫ ψ - q) (by` as an intermediate fact.

Rewrite using `[F.map_sub, ModuleCat.hom_sub, LinearMap.sub_apply, F.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, ht n, hψ, sub_self])`. Conclude with `sub_eq_zero.mp this`. Introduce `y hy`. Establish `h0 : (t n ≫ ψ).hom y = 0`. Rewrite using `[ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.mem_ker.mp hy, map_zero]`.

Rewrite `h0` using `[heq]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mp h0`. Establish `hsurjT : ∀ n, Function.Surjective (t n).hom`. Introduce `n`. Set `C : ModuleCat.{0} Λ` to `ModuleCat.of Λ (M0 (n + 1) ⧸ LinearMap.range (t n).hom)`.

Set `π : M0 (n + 1) ⟶ C` to `ModuleCat.ofHom (LinearMap.range (t n).hom).mkQ`. Establish `hCkill : ∀ x ∈ maximalIdeal Λ ^ (n + 1), ∀ y : C, x • y = 0`. Introduce `x hx y`. Take `⟨z, rfl⟩` from `Submodule.mkQ_surjective _ y`. Rewrite using `[← map_smul, hkill (n + 1) x hx z, map_zero]`.

Establish `htπ : t n ≫ π = 0`. Use extensionality with `z`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩`. Establish `hπ : π = 0` using `hmin0 (n + 1) C (htors C _ hCkill) π (by`. Rewrite using `[← ht n, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← F.map_comp, htπ, F.map_zero]`.

Use the proof step `rfl)`. Introduce `y`. Establish `h0 : π.hom y = 0` using `by rw [hπ]; rfl`. Conclude with `LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp h0)`. Take `⟨a, p, hp, hpt, hp0⟩` from `GlobalTheory.T.exists_compatible_generators_tower_local_ring Λ (fun n => M0 (n + 1)) (fun n => (t n).hom) hsurjT (fun n => (hkerT n).trans (Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero n))))`.

Set `N : Submodule Λ (Fin a → Λ)` to `⨅ n, LinearMap.ker (p n)`. Establish `hN' : ∀ n, LinearMap.ker (p n) ≤ N ⊔ maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ))`. Use `GlobalTheory.T.chain_le_iInf_sup_pow_smul_top_of_precomplete Λ (maximalIdeal Λ) a (fun n => LinearMap.ker (p n)) ?_ ?_ ?_` and prove the remaining obligations. Introduce `n c hc show p n c = 0`. Rewrite using `[← hpt n, LinearMap.comp_apply, LinearMap.mem_ker.mp hc, map_zero]`.

Introduce `n`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr c _`. Rewrite using `[LinearMap.mem_ker, map_smul]`. Conclude with `hkill (n + 1) r hr _`.

Introduce `n c hc`. Establish `h1 : (t n).hom (p (n + 1) c) = 0`. Rewrite using `[← LinearMap.comp_apply, hpt n]`. Conclude with `hc`. Establish `h2` using `hkerT n (LinearMap.mem_ker.mpr h1)`.

Establish `h3 : maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (M0 (n + 1 + 1))) = (maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ))).map (p (n + 1))`. Rewrite using `[Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hp (n + 1))]`. Rewrite `h2` using `[h3]`. Take `⟨d, hd, hdc⟩` from `h2`. Use `Submodule.mem_sup.mpr ⟨c - d, ?_, d, hd, sub_add_cancel c d⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.mem_ker, map_sub, hdc, sub_self]`. Take `⟨e, he⟩` from `assemble (Λ := Λ) F hcol (fun n => M0 (n + 1)) (fun n => ξ0 (n + 1)) t ht (fun n => hmin0 (n + 1)) (fun n => huniv0 (n + 1)) p hp (fun n c => LinearMap.congr_fun (hpt n) c) N (fun n => iInf_le (fun n => LinearMap.ker (p n)) n) hN'`. Establish `hNm : ∀ c ∈ N, ∀ i, c i ∈ maximalIdeal Λ` using `fun c hc i => hp0 c (LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hc 0)) i`. Take `⟨v, hv⟩` from `few_relations F hobs hsimple hres N hNm e he`. Establish `hker : ∀ (B : ModuleCat.{0} Λ), LinearMap.ker (matAct (M` using `B) (fun b i => (v b : Fin a → Λ) i)) = sol N B := by`.

Introduce `B`. Use extensionality with `x`. Rewrite using `[LinearMap.mem_ker, mem_sol]`. Establish `hx : ∀ b, matAct (M` using `B) (fun b i => (v b : Fin a → Λ) i) x b = ∑ i, (v b : Fin a → Λ) i • x i := fun b => by simp [matAct]`. Prove the components needed by the constructor for the conclusion.

Introduce `h0 c hc`. Establish `hc' : (⟨c, hc⟩ : N) ∈ Submodule.span Λ (Set.range v)`. Rewrite using `[hv]`. Conclude with `Submodule.mem_top`. Take `⟨d, hd⟩` from `(Submodule.mem_span_range_iff_exists_fun Λ).mp hc'`.

Establish `hd' : ∑ b, d b • (v b : Fin a → Λ) = c`. Use `congrArg Subtype.val hd` as an intermediate fact. Simplify `this` using `only [Submodule.coe_sum, Submodule.coe_smul]`. Establish `hb : ∀ b, ∑ i, (v b : Fin a → Λ) i • x i = 0` using `fun b => by`. Rewrite using `[← hx b, h0]`.

Both sides reduce to the same expression. Rewrite using `[← hd']`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul, Finset.smul_sum]`. Conclude with `Finset.sum_comm`.

Use `_ = 0 := Finset.sum_eq_zero fun b _ => by rw [hb b, smul_zero]`. Introduce `h`. Use function extensionality and compare the values at `b`. Rewrite using `[hx b]`. Conclude with `h _ (v b).2`.

Use `⟨a, fun b i => (v b : Fin a → Λ) i, fun b i => (mem_maximalIdeal _).mp (hNm _ (v b).2 i), fun B hB => (LinearEquiv.ofEq _ _ (hker B)).trans (e B hB), fun B B' hB hB' f x x' hx => ?_⟩` and prove the remaining obligations. Conclude with `he B B' hB hB' f (LinearEquiv.ofEq _ _ (hker B) x) (LinearEquiv.ofEq _ _ (hker B') x') hx`.
-/
theorem kernelRep : KernelRep := by
  unfold KernelRep
  intro Λ _ _ _ _ _ F _ _ hlex hcol hobs
  classical
  have hres := residue_kill (Λ := Λ)
  have hsimple := residue_simple (Λ := Λ)
  have htors : ∀ (B : ModuleCat.{0} Λ) (n : ℕ), (∀ x ∈ maximalIdeal Λ ^ n, ∀ y : B, x • y = 0) → Tors Λ B :=
    fun B n h y => ⟨n, fun x hx => h x hx y⟩
  have hFk : Finite (F.obj (ModuleCat.of Λ (ResidueField Λ))) := by
    have hKt : Tors Λ (ModuleCat.of Λ (ResidueField Λ)) :=
      htors _ 1 (fun r hr y => by rw [pow_one] at hr; exact hres r hr y)
    exact (hobs (ModuleCat.of Λ (ResidueField Λ)) (ModuleCat.of Λ (ResidueField Λ)) (ModuleCat.of Λ PUnit.{1})
      hsimple hKt (𝟙 _) 0 (fun _ _ h => h) (fun y => ⟨fun _ => ⟨y, rfl⟩, fun _ => rfl⟩)
      (fun _ => ⟨0, rfl⟩)).1
  choose M0 ξ0 hfin hkill hmin0 huniv0 using GlobalTheory.T.leftExact_functor_representable_torsion_modules Λ F hlex hFk
  have : ∀ n, Finite (M0 n) := hfin
  have htr : ∀ n, ∃ t : M0 (n + 1 + 1) ⟶ M0 (n + 1), (F.map t).hom (ξ0 (n + 1 + 1)) = ξ0 (n + 1) :=
    fun n => huniv0 (n + 1 + 1) (M0 (n + 1)) (hfin (n + 1))
      (fun x hx y => hkill (n + 1) x (Ideal.pow_le_pow_right (Nat.le_succ _) hx) y) (ξ0 (n + 1))
  choose t ht using htr
  have hkerT : ∀ n, LinearMap.ker (t n).hom ≤
      maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (M0 (n + 1 + 1))) := by
    intro n
    let Q : ModuleCat.{0} Λ :=
      ModuleCat.of Λ (M0 (n + 1 + 1) ⧸ maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (M0 (n + 1 + 1))))
    let q : M0 (n + 1 + 1) ⟶ Q := ModuleCat.ofHom (Submodule.mkQ _)
    have hQkill : ∀ x ∈ maximalIdeal Λ ^ (n + 1), ∀ y : Q, x • y = 0 := by
      intro x hx y
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hx Submodule.mem_top
    have hQfin : Finite Q := Finite.of_surjective _ (Submodule.mkQ_surjective
      (maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (M0 (n + 1 + 1)))))
    obtain ⟨ψ, hψ⟩ := huniv0 (n + 1) Q hQfin hQkill ((F.map q).hom (ξ0 (n + 1 + 1)))
    have heq : t n ≫ ψ = q := by
      have := hmin0 (n + 1 + 1) Q (htors Q _ hQkill) (t n ≫ ψ - q) (by
        rw [F.map_sub, ModuleCat.hom_sub, LinearMap.sub_apply, F.map_comp, ModuleCat.hom_comp,
          LinearMap.comp_apply, ht n, hψ, sub_self])
      exact sub_eq_zero.mp this
    intro y hy
    have h0 : (t n ≫ ψ).hom y = 0 := by
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.mem_ker.mp hy, map_zero]
    rw [heq] at h0
    exact (Submodule.Quotient.mk_eq_zero _).mp h0
  have hsurjT : ∀ n, Function.Surjective (t n).hom := by
    intro n
    let C : ModuleCat.{0} Λ := ModuleCat.of Λ (M0 (n + 1) ⧸ LinearMap.range (t n).hom)
    let π : M0 (n + 1) ⟶ C := ModuleCat.ofHom (LinearMap.range (t n).hom).mkQ
    have hCkill : ∀ x ∈ maximalIdeal Λ ^ (n + 1), ∀ y : C, x • y = 0 := by
      intro x hx y
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [← map_smul, hkill (n + 1) x hx z, map_zero]
    have htπ : t n ≫ π = 0 := by
      ext z
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩
    have hπ : π = 0 := hmin0 (n + 1) C (htors C _ hCkill) π (by
      rw [← ht n, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← F.map_comp, htπ, F.map_zero]
      rfl)
    intro y
    have h0 : π.hom y = 0 := by rw [hπ]; rfl
    exact LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp h0)
  obtain ⟨a, p, hp, hpt, hp0⟩ := GlobalTheory.T.exists_compatible_generators_tower_local_ring Λ (fun n => M0 (n + 1)) (fun n => (t n).hom) hsurjT
    (fun n => (hkerT n).trans (Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero n))))
  let N : Submodule Λ (Fin a → Λ) := ⨅ n, LinearMap.ker (p n)
  have hN' : ∀ n, LinearMap.ker (p n) ≤ N ⊔ maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
    refine GlobalTheory.T.chain_le_iInf_sup_pow_smul_top_of_precomplete Λ (maximalIdeal Λ) a (fun n => LinearMap.ker (p n)) ?_ ?_ ?_
    · intro n c hc
      show p n c = 0
      rw [← hpt n, LinearMap.comp_apply, LinearMap.mem_ker.mp hc, map_zero]
    · intro n
      rw [Submodule.smul_le]
      intro r hr c _
      rw [LinearMap.mem_ker, map_smul]
      exact hkill (n + 1) r hr _
    · intro n c hc
      have h1 : (t n).hom (p (n + 1) c) = 0 := by
        rw [← LinearMap.comp_apply, hpt n]
        exact hc
      have h2 := hkerT n (LinearMap.mem_ker.mpr h1)
      have h3 : maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (M0 (n + 1 + 1))) =
          (maximalIdeal Λ ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ))).map (p (n + 1)) := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hp (n + 1))]
      rw [h3] at h2
      obtain ⟨d, hd, hdc⟩ := h2
      refine Submodule.mem_sup.mpr ⟨c - d, ?_, d, hd, sub_add_cancel c d⟩
      rw [LinearMap.mem_ker, map_sub, hdc, sub_self]
  obtain ⟨e, he⟩ := assemble (Λ := Λ) F hcol (fun n => M0 (n + 1)) (fun n => ξ0 (n + 1)) t ht
    (fun n => hmin0 (n + 1)) (fun n => huniv0 (n + 1)) p hp (fun n c => LinearMap.congr_fun (hpt n) c) N
    (fun n => iInf_le (fun n => LinearMap.ker (p n)) n) hN'
  have hNm : ∀ c ∈ N, ∀ i, c i ∈ maximalIdeal Λ := fun c hc i =>
    hp0 c (LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hc 0)) i
  obtain ⟨v, hv⟩ := few_relations F hobs hsimple hres N hNm e he
  have hker : ∀ (B : ModuleCat.{0} Λ),
      LinearMap.ker (matAct (M := B) (fun b i => (v b : Fin a → Λ) i)) = sol N B := by
    intro B
    ext x
    rw [LinearMap.mem_ker, mem_sol]
    have hx : ∀ b, matAct (M := B) (fun b i => (v b : Fin a → Λ) i) x b = ∑ i, (v b : Fin a → Λ) i • x i :=
      fun b => by simp [matAct]
    constructor
    · intro h0 c hc
      have hc' : (⟨c, hc⟩ : N) ∈ Submodule.span Λ (Set.range v) := by
        rw [hv]
        exact Submodule.mem_top
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).mp hc'
      have hd' : ∑ b, d b • (v b : Fin a → Λ) = c := by
        have := congrArg Subtype.val hd
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using this
      have hb : ∀ b, ∑ i, (v b : Fin a → Λ) i • x i = 0 := fun b => by
        rw [← hx b, h0]
        rfl
      rw [← hd']
      calc ∑ i, (∑ b, d b • (v b : Fin a → Λ)) i • x i
          = ∑ b, d b • ∑ i, (v b : Fin a → Λ) i • x i := by
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul,
              Finset.smul_sum]
            exact Finset.sum_comm
        _ = 0 := Finset.sum_eq_zero fun b _ => by rw [hb b, smul_zero]
    · intro h
      funext b
      rw [hx b]
      exact h _ (v b).2
  refine ⟨a, fun b i => (v b : Fin a → Λ) i, fun b i => (mem_maximalIdeal _).mp (hNm _ (v b).2 i),
    fun B hB => (LinearEquiv.ofEq _ _ (hker B)).trans (e B hB), fun B B' hB hB' f x x' hx => ?_⟩
  exact he B B' hB hB' f (LinearEquiv.ofEq _ _ (hker B) x) (LinearEquiv.ofEq _ _ (hker B') x') hx

end GlobalTheory.KRep
