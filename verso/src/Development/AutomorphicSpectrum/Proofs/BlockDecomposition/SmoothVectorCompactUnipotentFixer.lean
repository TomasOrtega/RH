import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosedStatement
import GroundTheory.AutomorphicForms.IwahoriFactorization
import GroundTheory.AutomorphicForms.GeometricLemmaCellSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open GroundTheory.Automorphic.GLnLocal
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.Rodier.OpenBump

/- English proof (translation)
Establish `key : ∀ p q : H, (p : G)⁻¹ * q ∈ K → σ q v = σ p v`. Introduce `p q hpq`. Establish `h1 : σ (p⁻¹ * q) v = v` using `hv _ (by simpa using hpq)`. Establish `h2 : q = p * (p⁻¹ * q)` using `by group`. Combine the equalities or inequalities in the displayed calculation.

Set `S : G → Prop` to `fun x => ∃ p : H, (p : G)⁻¹ * x ∈ K`. Set `pick : G → H` to `fun x => if h : S x then h.choose else 1`. Establish `pick_spec : ∀ x, S x → ((pick x : H) : G)⁻¹ * x ∈ K`. Introduce `x h`. Simplify using `only [pick, dif_pos h]`.

Conclude with `h.choose_spec`. Set `F : G → W` to `fun x => if S x then σ (pick x) v else 0`. Establish `F_pos : ∀ x, S x → F x = σ (pick x) v` using `fun x h => if_pos h`. Establish `F_neg : ∀ x, ¬ S x → F x = 0` using `fun x h => if_neg h`. Establish `S_left : ∀ (q : H) x, S x → S (q * x)`.

Introduce and unpack `q x ⟨p, hp⟩`. Conclude with `⟨q * p, by simpa [mul_assoc] using hp⟩`. Establish `S_right : ∀ c ∈ K, ∀ x, S x → S (x * c)`. Introduce and unpack `c hc x ⟨p, hp⟩`. Conclude with `⟨p, by simpa [mul_assoc] using K.mul_mem hp hc⟩`.

Establish `hlaw : F ∈ indSpace H σ`. Introduce `q x`. Distinguish the cases in `hx : S x`. Establish `hqx` using `S_left q x hx`. Rewrite using `[F_pos _ hqx, F_pos _ hx, ← Module.End.mul_apply, ← map_mul]`.

Use `key _ _ ?_` and prove the remaining obligations. Establish `h3` using `K.mul_mem (pick_spec x hx) (K.inv_mem (pick_spec _ hqx))`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Subgroup.coe_mul]`. Use `group`.

Establish `hqx : ¬ S (q * x)` using `fun h => hx (by`. Use `S_left q⁻¹ _ h` as an intermediate fact. Simplify using `using this)`. Rewrite using `[F_neg _ hqx, F_neg _ hx, map_zero]`. Establish `hfix : ∀ c ∈ K, ∀ x, F (x * c) = F x`.

Introduce `c hc x`. Distinguish the cases in `hx : S x`. Establish `hxc` using `S_right c hc x hx`. Rewrite using `[F_pos _ hxc, F_pos _ hx]`. Use `key _ _ ?_` and prove the remaining obligations.

Establish `h3` using `K.mul_mem (K.mul_mem (pick_spec x hx) hc) (K.inv_mem (pick_spec _ hxc))`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use `group`. Establish `hxc : ¬ S (x * c)` using `fun h => hx (by`. Use `S_right c⁻¹ (K.inv_mem hc) _ h` as an intermediate fact.

Simplify using `using this)`. Rewrite using `[F_neg _ hxc, F_neg _ hx]`. Establish `hfix' : ∀ c ∈ K, ind H σ c ⟨F, hlaw⟩ = ⟨F, hlaw⟩` using `fun c hc => Subtype.ext (funext fun x => hfix c hc x)`. Establish `hsm : (⟨F, hlaw⟩ : indSpace H σ) ∈ smoothPart (ind H σ)` using `mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem) fun c hc => hfix' c hc)`. Use `⟨⟨⟨F, hlaw⟩, hsm⟩, fun g hg => ?_, fun κ hκ => ?_⟩` and prove the remaining obligations.

Establish `hS : S g`. Assume the negation of the conclusion as `hS`. Conclude with `hg (F_neg g hS)`. Conclude with `⟨pick g, (pick g).2, _, pick_spec g hS, by group⟩`. Establish `hS : S κ` using `⟨1, by simpa using hκ⟩ show F κ = v`.

Rewrite using `[F_pos κ hS]`. Use `hv _ ?_` and prove the remaining obligations. Establish `h3` using `K.mul_mem hκ (K.inv_mem (pick_spec κ hS))`. Simplify using `using h3`.
-/
theorem exists_smInd_bump {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H K : Subgroup G) (hK : IsOpen (K : Set G))
    (σ : Representation ℂ H W) (v : W) (hv : ∀ c : H, (c : G) ∈ K → σ c v = v) :
    ∃ f : smoothPart (ind H σ), (∀ g, f.1.1 g ≠ 0 → ∃ p ∈ H, ∃ κ ∈ K, g = p * κ) ∧
      ∀ κ ∈ K, f.1.1 κ = v := by
  classical
  have key : ∀ p q : H, (p : G)⁻¹ * q ∈ K → σ q v = σ p v := by
    intro p q hpq
    have h1 : σ (p⁻¹ * q) v = v := hv _ (by simpa using hpq)
    have h2 : q = p * (p⁻¹ * q) := by group
    calc σ q v = σ (p * (p⁻¹ * q)) v := by rw [← h2]
      _ = σ p (σ (p⁻¹ * q) v) := by rw [map_mul]; rfl
      _ = σ p v := by rw [h1]
  let S : G → Prop := fun x => ∃ p : H, (p : G)⁻¹ * x ∈ K
  let pick : G → H := fun x => if h : S x then h.choose else 1
  have pick_spec : ∀ x, S x → ((pick x : H) : G)⁻¹ * x ∈ K := by
    intro x h
    simp only [pick, dif_pos h]
    exact h.choose_spec
  let F : G → W := fun x => if S x then σ (pick x) v else 0
  have F_pos : ∀ x, S x → F x = σ (pick x) v := fun x h => if_pos h
  have F_neg : ∀ x, ¬ S x → F x = 0 := fun x h => if_neg h
  have S_left : ∀ (q : H) x, S x → S (q * x) := by
    rintro q x ⟨p, hp⟩
    exact ⟨q * p, by simpa [mul_assoc] using hp⟩
  have S_right : ∀ c ∈ K, ∀ x, S x → S (x * c) := by
    rintro c hc x ⟨p, hp⟩
    exact ⟨p, by simpa [mul_assoc] using K.mul_mem hp hc⟩
  have hlaw : F ∈ indSpace H σ := by
    intro q x
    by_cases hx : S x
    · have hqx := S_left q x hx
      rw [F_pos _ hqx, F_pos _ hx, ← Module.End.mul_apply, ← map_mul]
      refine key _ _ ?_
      have h3 := K.mul_mem (pick_spec x hx) (K.inv_mem (pick_spec _ hqx))
      convert h3 using 1
      simp only [Subgroup.coe_mul]
      group
    · have hqx : ¬ S (q * x) := fun h => hx (by
        have := S_left q⁻¹ _ h
        simpa using this)
      rw [F_neg _ hqx, F_neg _ hx, map_zero]
  have hfix : ∀ c ∈ K, ∀ x, F (x * c) = F x := by
    intro c hc x
    by_cases hx : S x
    · have hxc := S_right c hc x hx
      rw [F_pos _ hxc, F_pos _ hx]
      refine key _ _ ?_
      have h3 := K.mul_mem (K.mul_mem (pick_spec x hx) hc) (K.inv_mem (pick_spec _ hxc))
      convert h3 using 1
      group
    · have hxc : ¬ S (x * c) := fun h => hx (by
        have := S_right c⁻¹ (K.inv_mem hc) _ h
        simpa using this)
      rw [F_neg _ hxc, F_neg _ hx]
  have hfix' : ∀ c ∈ K, ind H σ c ⟨F, hlaw⟩ = ⟨F, hlaw⟩ :=
    fun c hc => Subtype.ext (funext fun x => hfix c hc x)
  have hsm : (⟨F, hlaw⟩ : indSpace H σ) ∈ smoothPart (ind H σ) :=
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem) fun c hc => hfix' c hc)
  refine ⟨⟨⟨F, hlaw⟩, hsm⟩, fun g hg => ?_, fun κ hκ => ?_⟩
  · have hS : S g := by
      by_contra hS
      exact hg (F_neg g hS)
    exact ⟨pick g, (pick g).2, _, pick_spec g hS, by group⟩
  · have hS : S κ := ⟨1, by simpa using hκ⟩
    show F κ = v
    rw [F_pos κ hS]
    refine hv _ ?_
    have h3 := K.mul_mem hκ (K.inv_mem (pick_spec κ hS))
    simpa using h3

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨h3, h4⟩` from `(mem_unipRadLower k).1 h2`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Take `⟨⟨a, i⟩, rfl⟩` from `e.surjective i`. Take `⟨⟨b, j⟩, rfl⟩` from `e.surjective j`. Establish `hne : ∀ c : α, ∀ (i' : m c) (b' : α) (j' : m b'), c ≠ b' → (1 : Matrix n n k) (e ⟨c, i'⟩) (e ⟨b', j'⟩) = 0`.

Introduce `c i' b' j' hcb`. Use `Matrix.one_apply_ne fun h' => hcb ?_` and prove the remaining obligations. Use `e.injective h'` as an intermediate fact. Conclude with `congrArg Sigma.fst this`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases.

Rewrite using `[(mem_parabLower_iff k).1 h3 a b i j hab, Units.val_one, hne a i b j hab.ne]`. Rewrite using `[h4 a i j, Units.val_one]`. Distinguish the cases in `e' : i = j`. Substitute `e'` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.one_apply_ne e', Matrix.one_apply_ne]`. Introduce `h'`. Conclude with `e' (by simpa using e.injective h')`. Rewrite using `[mem_parab_iff.1 h1 a b i j hab, Units.val_one, hne a i b j hab.ne']`.
-/
theorem eq_one_of_mem_parab_of_mem_lower {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) {x : GL n k} (h1 : x ∈ parab k e) (h2 : x ∈ unipRadLower k e) : x = 1 := by
  obtain ⟨h3, h4⟩ := (mem_unipRadLower k).1 h2
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  have hne : ∀ c : α, ∀ (i' : m c) (b' : α) (j' : m b'), c ≠ b' →
      (1 : Matrix n n k) (e ⟨c, i'⟩) (e ⟨b', j'⟩) = 0 := by
    intro c i' b' j' hcb
    refine Matrix.one_apply_ne fun h' => hcb ?_
    have := e.injective h'
    exact congrArg Sigma.fst this
  rcases lt_trichotomy a b with hab | rfl | hab
  · rw [(mem_parabLower_iff k).1 h3 a b i j hab, Units.val_one, hne a i b j hab.ne]
  · rw [h4 a i j, Units.val_one]
    by_cases e' : i = j
    · subst e'; simp
    · rw [Matrix.one_apply_ne e', Matrix.one_apply_ne]
      intro h'
      exact e' (by simpa using e.injective h')
  · rw [mem_parab_iff.1 h1 a b i j hab, Units.val_one, hne a i b j hab.ne']

/- English proof (translation)
Take `⟨x, hx, y, hy, z, hz, rfl⟩` from `GroundTheory.Automorphic.Parabolic.congruenceSubgroup_iwahoriFactorization' (blk (stdBlocks d hd)) hm κ hκ`. Establish `up : ∀ g ∈ GroundTheory.Automorphic.Iwasawa.blockUpper k N (blk (stdBlocks d hd)), g ∈ parab k (stdBlocks d hd)` using `fun g hg => (GroundTheory.Automorphic.Iwasawa.mem_blockUpper k N).1 hg`. Use `⟨x * y, (parab k _).mul_mem (up _ (GroundTheory.Automorphic.Parabolic.unipotentRadical_le_blockUpper hx.2)) (up _ (GroundTheory.Automorphic.Parabolic.levi_le_blockUpper hy.2)), z, hz.1, ?_, rfl⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `GroundTheory.Automorphic.Parabolic.mem_unipotentRadical.1 hz.2`. Establish `h1'` using `(GroundTheory.Automorphic.Iwasawa.mem_blockUpper k N).1 h1`.

Use `(mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j hab => h1' ?_, fun a i j => ?_⟩` and prove the remaining obligations. Simplify `hab` using `[blk]`. Rewrite using `[h2 _ _ (by simp [blk])]`. Distinguish the cases in `e' : i = j`. Substitute `e'` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne e', Matrix.one_apply_ne]`. Introduce `h'`. Conclude with `e' (by simpa using (stdBlocks d hd).injective h')`.
-/
theorem exists_parab_mul_lower {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {m : ℕ} (hm : 1 ≤ m)
    {κ : GL (Fin N) k} (hκ : κ ∈ congruenceSubgroup k N m) :
    ∃ q ∈ parab k (stdBlocks d hd), ∃ z ∈ congruenceSubgroup k N m,
      z ∈ unipRadLower k (stdBlocks d hd) ∧ κ = q * z := by
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
    GroundTheory.Automorphic.Parabolic.congruenceSubgroup_iwahoriFactorization' (blk (stdBlocks d hd)) hm κ hκ
  have up : ∀ g ∈ GroundTheory.Automorphic.Iwasawa.blockUpper k N (blk (stdBlocks d hd)), g ∈ parab k (stdBlocks d hd) :=
    fun g hg => (GroundTheory.Automorphic.Iwasawa.mem_blockUpper k N).1 hg
  refine ⟨x * y, (parab k _).mul_mem (up _ (GroundTheory.Automorphic.Parabolic.unipotentRadical_le_blockUpper hx.2))
    (up _ (GroundTheory.Automorphic.Parabolic.levi_le_blockUpper hy.2)), z, hz.1, ?_, rfl⟩
  obtain ⟨h1, h2⟩ := GroundTheory.Automorphic.Parabolic.mem_unipotentRadical.1 hz.2
  have h1' := (GroundTheory.Automorphic.Iwasawa.mem_blockUpper k N).1 h1
  refine (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j hab => h1' ?_, fun a i j => ?_⟩
  · simpa [blk] using hab
  · rw [h2 _ _ (by simp [blk])]
    by_cases e' : i = j
    · subst e'; simp
    · rw [Matrix.one_apply_ne e', Matrix.one_apply_ne]
      intro h'
      exact e' (by simpa using (stdBlocks d hd).injective h')

/- English proof (translation)
Establish `hs` using `isSmooth_twist hρ (isSmoothChar_deltaHalf k (m := fun a => Fin (d a))) v`. Establish `hpre` using `hs.preimage (ProdIrr.continuous_leviProj (stdBlocks d hd))`. Take `⟨U, hU, hUe⟩` from `isOpen_induced_iff.1 hpre`. Establish `hw : IsOpen ((whitChar ψ N).ker : Set (unipB k (Fin N)))` using `GlobalTheory.Whittaker.isSmoothChar_whitChar hψ`. Take `⟨U₂, hU₂, hUe₂⟩` from `isOpen_induced_iff.1 hw`.

Establish `h1 : (1 : GL (Fin N) k) ∈ U`. Establish `h2 : (1 : parab k (stdBlocks d hd)) ∈ Subtype.val ⁻¹' U`. Rewrite using `[hUe]`. Simplify using the standard rewrite rules. Conclude with `h2`.

Establish `h1₂ : (1 : GL (Fin N) k) ∈ U₂`. Establish `h2 : (1 : unipB k (Fin N)) ∈ Subtype.val ⁻¹' U₂`. Rewrite using `[hUe₂]`. Conclude with `one_mem _`. Conclude with `h2`.

Take `⟨m, -, hm⟩` from `(hasBasis_nhds_one k N).mem_iff.1 ((hU.inter hU₂).mem_nhds ⟨h1, h1₂⟩)`. Use `⟨m + 1, by omega, fun c hc => ?_, fun l hl hlK => ?_⟩` and prove the remaining obligations. Establish `h2 : c ∈ Subtype.val ⁻¹' U` using `(hm (congruenceSubgroup_antitone k N (Nat.le_succ m) hc)).1`. Rewrite `h2` using `[hUe]`. Conclude with `h2`.

Establish `h2 : (⟨l, hl⟩ : unipB k (Fin N)) ∈ Subtype.val ⁻¹' U₂` using `(hm (congruenceSubgroup_antitone k N (Nat.le_succ m) hlK)).2`. Rewrite `h2` using `[hUe₂]`. Conclude with `h2`.
-/
theorem exists_level (ψ : AddChar k Circle) (hψ : Continuous ψ) {h N : ℕ} (d : Fin h → ℕ)
    (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (hρ : IsSmooth ρ) (v : W) :
    ∃ m, 1 ≤ m ∧ (∀ c : parab k (stdBlocks d hd), (c : GL (Fin N) k) ∈ congruenceSubgroup k N m →
        ((twist ρ (deltaHalf k fun a => Fin (d a))).comp (leviProj k (stdBlocks d hd))) c v = v) ∧
      ∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ congruenceSubgroup k N m →
        whitChar ψ N ⟨l, hl⟩ = 1 := by
  have hs := isSmooth_twist hρ (isSmoothChar_deltaHalf k (m := fun a => Fin (d a))) v
  have hpre := hs.preimage (ProdIrr.continuous_leviProj (stdBlocks d hd))
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hpre
  have hw : IsOpen ((whitChar ψ N).ker : Set (unipB k (Fin N))) :=
    GlobalTheory.Whittaker.isSmoothChar_whitChar hψ
  obtain ⟨U₂, hU₂, hUe₂⟩ := isOpen_induced_iff.1 hw
  have h1 : (1 : GL (Fin N) k) ∈ U := by
    have h2 : (1 : parab k (stdBlocks d hd)) ∈ Subtype.val ⁻¹' U := by
      rw [hUe]
      simp
    exact h2
  have h1₂ : (1 : GL (Fin N) k) ∈ U₂ := by
    have h2 : (1 : unipB k (Fin N)) ∈ Subtype.val ⁻¹' U₂ := by
      rw [hUe₂]
      exact one_mem _
    exact h2
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_one k N).mem_iff.1 ((hU.inter hU₂).mem_nhds ⟨h1, h1₂⟩)
  refine ⟨m + 1, by omega, fun c hc => ?_, fun l hl hlK => ?_⟩
  · have h2 : c ∈ Subtype.val ⁻¹' U := (hm (congruenceSubgroup_antitone k N (Nat.le_succ m) hc)).1
    rw [hUe] at h2
    exact h2
  · have h2 : (⟨l, hl⟩ : unipB k (Fin N)) ∈ Subtype.val ⁻¹' U₂ :=
      (hm (congruenceSubgroup_antitone k N (Nat.le_succ m) hlK)).2
    rw [hUe₂] at h2
    exact h2

/- English proof (translation)
Introduce `k _ _ _ _ ψ hψ h N d hd W _ _ ρ hρ v`. Take `⟨m, hm1, hσ, hW⟩` from `exists_level ψ hψ d hd ρ hρ v`. Take `⟨hI1, -, hI3⟩` from `GlobalTheory.T.open_cell_unipotent_uniqueness_closed k h N d hd`. Establish `hKo` using `isOpen_congruenceSubgroup k N m`. Establish `hKc` using `isCompact_congruenceSubgroup k N m`.

Use `set K := congruenceSubgroup k N m with hKdef`. Use `set w := pm k (wOpen d hd) with hwdef`. Establish `hwI : w ∈ integralGL k N` using `GroundTheory.Automorphic.Parabolic.permGL_mem_integralGL _`. Establish `hconj : ∀ x ∈ K, w * x * w⁻¹ ∈ K` using `fun x hx => conj_mem_congruenceSubgroup k N hwI hx`. Establish `hconj' : ∀ x ∈ K, w⁻¹ * x * w ∈ K` using `fun x hx => by`.

Simplify using `using conj_mem_congruenceSubgroup k N ((integralGL k N).inv_mem hwI) hx`. Take `⟨f₀, hsup, hval⟩` from `exists_smInd_bump (parab k (stdBlocks d hd)) K hKo ((twist ρ (deltaHalf k fun a => Fin (d a))).comp (leviProj k (stdBlocks d hd))) v hσ`. Set `f : IndSp (stdBlocks d hd) ρ` to `smInd (parab k (stdBlocks d hd)) ((twist ρ (deltaHalf k fun a => Fin (d a))).comp (leviProj k (stdBlocks d hd))) w⁻¹ f₀`. Establish `hf : ∀ g, f.1.1 g = f₀.1.1 (g * w⁻¹)` using `fun _ => rfl`. Set `L₀ : Subgroup (GL (Fin N) k)` to `unipU k d hd ⊓ K.comap (MulAut.conj w).toMonoidHom`.

Establish `memL : ∀ u, u ∈ L₀ ↔ u ∈ unipU k d hd ∧ w * u * w⁻¹ ∈ K` using `fun u => Iff.rfl`. Establish `memU : ∀ u ∈ unipU k d hd, w * u * w⁻¹ ∈ unipRadLower k (stdBlocks d hd)` using `fun u hu => hu.2`. Establish `hcont : Continuous fun g : GL (Fin N) k => w⁻¹ * g * w` using `by fun_prop`. Establish `hcont' : Continuous fun g : GL (Fin N) k => w * g * w⁻¹` using `by fun_prop`. Use `⟨L₀, inf_le_left, ?_, ⟨(fun g => w * g * w⁻¹) ⁻¹' (K : Set _), hKo.preimage hcont', ?_⟩, ?_, f, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hset : (L₀ : Set (GL (Fin N) k)) = ((fun g => w⁻¹ * g * w) '' (K : Set (GL (Fin N) k))) ∩ (unipU k d hd : Set _)`. Use extensionality with `u`. Prove the components needed by the constructor for the conclusion. Introduce `hu`. Conclude with `⟨⟨_, ((memL u).1 hu).2, by group⟩, ((memL u).1 hu).1⟩`.

Introduce and unpack `⟨⟨x, hx, rfl⟩, hu⟩`. Use `(memL _).2 ⟨hu, ?_⟩` and prove the remaining obligations. Establish `: w * (w⁻¹ * x * w) * w⁻¹ = x` using `by group`. Rewrite using `[this]`. Conclude with `hx`.

Rewrite using `[hset]`. Conclude with `(hKc.image hcont).inter_right hI3`. Use extensionality with `u`. Conclude with `⟨fun hu => (memL u).2 ⟨hu.2, hu.1⟩, fun hu => ⟨((memL u).1 hu).2, ((memL u).1 hu).1⟩⟩`. Introduce `l hl hlL`.

Use `hW l hl ?_` and prove the remaining obligations. Use `hconj' _ ((memL l).1 hlL).2` as an intermediate fact. Establish `e : w⁻¹ * (w * l * w⁻¹) * w = l` using `by group`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Introduce `g hg`.

Rewrite `hg` using `[hf]`. Take `⟨p, hp, κ, hκ, e⟩` from `hsup _ hg`. Take `⟨q, hq, z, hz, hzl, rfl⟩` from `exists_parab_mul_lower d hd hm1 hκ`. Use `⟨p * q, (parab k _).mul_mem hp hq, w⁻¹ * z * w, (hI1 z hzl).1, ?_⟩` and prove the remaining obligations. Establish `e2 : g = p * (q * z) * w`.

Rewrite using `[← e]`. Use `group`. Use `show g = p * q * w * (w⁻¹ * z * w)`. Rewrite using `[e2]`. Use `group`.

Introduce `u hu`. Use `hval _ ((memL u).1 hu).2` as an intermediate fact. Rewrite using `[hf]`. Conclude with `this`. Introduce `u hu huL`.

Rewrite using `[hf]`. Assume the negation of the conclusion as `hne`. Take `⟨p, hp, κ, hκ, e⟩` from `hsup _ hne`. Take `⟨q, hq, z, hz, hzl, rfl⟩` from `exists_parab_mul_lower d hd hm1 hκ`. Establish `hx` using `memU u hu`.

Establish `h1 : (w * u * w⁻¹) * z⁻¹ = 1`. Use `eq_one_of_mem_parab_of_mem_lower (stdBlocks d hd) ?_ ((unipRadLower k _).mul_mem hx ((unipRadLower k _).inv_mem hzl))` and prove the remaining obligations. Rewrite using `[e]`. Establish `: p * (q * z) * z⁻¹ = p * q` using `by group`. Rewrite using `[this]`.

Conclude with `(parab k _).mul_mem hp hq`. Establish `h2 : w * u * w⁻¹ = z` using `by rwa [mul_inv_eq_one] at h1`. Conclude with `huL ((memL u).2 ⟨hu, h2 ▸ hz⟩)`.
-/
theorem exists_openFns_bump : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∀ v : W, ∃ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd ∧ IsCompact (L₀ : Set (GL (Fin N) k)) ∧ (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) ∧ (∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ L₀ → whitChar ψ N ⟨l, hl⟩ = 1) ∧ ∃ f ∈ openFns d hd ρ, (∀ u ∈ L₀, f.1.1 (pm k (wOpen d hd) * u) = v) ∧ ∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1 (pm k (wOpen d hd) * u) = 0 := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ hρ v
  obtain ⟨m, hm1, hσ, hW⟩ := exists_level ψ hψ d hd ρ hρ v
  obtain ⟨hI1, -, hI3⟩ := GlobalTheory.T.open_cell_unipotent_uniqueness_closed k h N d hd
  have hKo := isOpen_congruenceSubgroup k N m
  have hKc := isCompact_congruenceSubgroup k N m
  set K := congruenceSubgroup k N m with hKdef
  set w := pm k (wOpen d hd) with hwdef
  have hwI : w ∈ integralGL k N := GroundTheory.Automorphic.Parabolic.permGL_mem_integralGL _
  have hconj : ∀ x ∈ K, w * x * w⁻¹ ∈ K := fun x hx => conj_mem_congruenceSubgroup k N hwI hx
  have hconj' : ∀ x ∈ K, w⁻¹ * x * w ∈ K := fun x hx => by
    simpa using conj_mem_congruenceSubgroup k N ((integralGL k N).inv_mem hwI) hx
  obtain ⟨f₀, hsup, hval⟩ := exists_smInd_bump (parab k (stdBlocks d hd)) K hKo
    ((twist ρ (deltaHalf k fun a => Fin (d a))).comp (leviProj k (stdBlocks d hd))) v hσ
  let f : IndSp (stdBlocks d hd) ρ := smInd (parab k (stdBlocks d hd))
    ((twist ρ (deltaHalf k fun a => Fin (d a))).comp (leviProj k (stdBlocks d hd))) w⁻¹ f₀
  have hf : ∀ g, f.1.1 g = f₀.1.1 (g * w⁻¹) := fun _ => rfl
  let L₀ : Subgroup (GL (Fin N) k) := unipU k d hd ⊓ K.comap (MulAut.conj w).toMonoidHom
  have memL : ∀ u, u ∈ L₀ ↔ u ∈ unipU k d hd ∧ w * u * w⁻¹ ∈ K := fun u => Iff.rfl
  have memU : ∀ u ∈ unipU k d hd, w * u * w⁻¹ ∈ unipRadLower k (stdBlocks d hd) :=
    fun u hu => hu.2
  have hcont : Continuous fun g : GL (Fin N) k => w⁻¹ * g * w := by fun_prop
  have hcont' : Continuous fun g : GL (Fin N) k => w * g * w⁻¹ := by fun_prop
  refine ⟨L₀, inf_le_left, ?_, ⟨(fun g => w * g * w⁻¹) ⁻¹' (K : Set _), hKo.preimage hcont', ?_⟩,
    ?_, f, ?_, ?_, ?_⟩
  · have hset : (L₀ : Set (GL (Fin N) k)) =
        ((fun g => w⁻¹ * g * w) '' (K : Set (GL (Fin N) k))) ∩ (unipU k d hd : Set _) := by
      ext u
      constructor
      · intro hu
        exact ⟨⟨_, ((memL u).1 hu).2, by group⟩, ((memL u).1 hu).1⟩
      · rintro ⟨⟨x, hx, rfl⟩, hu⟩
        refine (memL _).2 ⟨hu, ?_⟩
        have : w * (w⁻¹ * x * w) * w⁻¹ = x := by group
        rw [this]
        exact hx
    rw [hset]
    exact (hKc.image hcont).inter_right hI3
  · ext u
    exact ⟨fun hu => (memL u).2 ⟨hu.2, hu.1⟩, fun hu => ⟨((memL u).1 hu).2, ((memL u).1 hu).1⟩⟩
  · intro l hl hlL
    refine hW l hl ?_
    have := hconj' _ ((memL l).1 hlL).2
    have e : w⁻¹ * (w * l * w⁻¹) * w = l := by group
    rwa [e] at this
  · intro g hg
    rw [hf] at hg
    obtain ⟨p, hp, κ, hκ, e⟩ := hsup _ hg
    obtain ⟨q, hq, z, hz, hzl, rfl⟩ := exists_parab_mul_lower d hd hm1 hκ
    refine ⟨p * q, (parab k _).mul_mem hp hq, w⁻¹ * z * w, (hI1 z hzl).1, ?_⟩
    have e2 : g = p * (q * z) * w := by
      rw [← e]
      group
    show g = p * q * w * (w⁻¹ * z * w)
    rw [e2]
    group
  · intro u hu
    have := hval _ ((memL u).1 hu).2
    rw [hf]
    exact this
  · intro u hu huL
    rw [hf]
    by_contra hne
    obtain ⟨p, hp, κ, hκ, e⟩ := hsup _ hne
    obtain ⟨q, hq, z, hz, hzl, rfl⟩ := exists_parab_mul_lower d hd hm1 hκ
    have hx := memU u hu
    have h1 : (w * u * w⁻¹) * z⁻¹ = 1 := by
      refine eq_one_of_mem_parab_of_mem_lower (stdBlocks d hd) ?_
        ((unipRadLower k _).mul_mem hx ((unipRadLower k _).inv_mem hzl))
      rw [e]
      have : p * (q * z) * z⁻¹ = p * q := by group
      rw [this]
      exact (parab k _).mul_mem hp hq
    have h2 : w * u * w⁻¹ = z := by rwa [mul_inv_eq_one] at h1
    exact huL ((memL u).2 ⟨hu, h2 ▸ hz⟩)

end GlobalTheory.CompanionTheory.Rodier.OpenBump

end
