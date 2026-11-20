import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import GroundTheory.AutomorphicForms.GLnLocal

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped Topology

namespace GlobalTheory.CompanionTheory.LeviAdm

/- English proof (translation)
Establish `key : ∀ p q : H, (p : G)⁻¹ * q ∈ K → ∀ w ∈ A, σ q w = σ p w`. Introduce `p q hpq w hw`. Establish `h1 : σ (p⁻¹ * q) w = w` using `hA _ (by simpa using hpq) w hw`. Establish `h2 : q = p * (p⁻¹ * q)` using `by group`. Combine the equalities or inequalities in the displayed calculation.

Set `S : G → Prop` to `fun x => ∃ p : H, (p : G)⁻¹ * x ∈ K`. Set `pick : G → H` to `fun x => if h : S x then h.choose else 1`. Establish `pick_spec : ∀ x, S x → ((pick x : H) : G)⁻¹ * x ∈ K`. Introduce `x h`. Simplify using `only [pick, dif_pos h]`.

Conclude with `h.choose_spec`. Set `F : A →ₗ[ℂ] (G → W)` to `LinearMap.pi fun x => if S x then (σ (pick x)).comp A.subtype else 0`. Establish `F_pos : ∀ (w : A) x, S x → F w x = σ (pick x) w`. Introduce `w x h`. Simplify using `[F, h]`.

Establish `F_neg : ∀ (w : A) x, ¬ S x → F w x = 0`. Introduce `w x h`. Simplify using `[F, h]`. Establish `S_left : ∀ (q : H) x, S x → S (q * x)`. Introduce and unpack `q x ⟨p, hp⟩`.

Conclude with `⟨q * p, by simpa [mul_assoc] using hp⟩`. Establish `S_right : ∀ c ∈ K, ∀ x, S x → S (x * c)`. Introduce and unpack `c hc x ⟨p, hp⟩`. Conclude with `⟨p, by simpa [mul_assoc] using K.mul_mem hp hc⟩`. Establish `hlaw : ∀ w : A, F w ∈ indSpace H σ`.

Introduce `w q x`. Distinguish the cases in `hx : S x`. Establish `hqx` using `S_left q x hx`. Rewrite using `[F_pos w _ hqx, F_pos w _ hx, ← Module.End.mul_apply, ← map_mul]`. Use `key _ _ ?_ w w.2` and prove the remaining obligations.

Establish `h3` using `K.mul_mem (pick_spec x hx) (K.inv_mem (pick_spec _ hqx))`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Subgroup.coe_mul]`. Use `group`. Establish `hqx : ¬ S (q * x)` using `fun h => hx (by`.

Use `S_left q⁻¹ _ h` as an intermediate fact. Simplify using `using this)`. Rewrite using `[F_neg w _ hqx, F_neg w _ hx, map_zero]`. Establish `hfix : ∀ (w : A), ∀ c ∈ K, ∀ x, F w (x * c) = F w x`. Introduce `w c hc x`.

Distinguish the cases in `hx : S x`. Establish `hxc` using `S_right c hc x hx`. Rewrite using `[F_pos w _ hxc, F_pos w _ hx]`. Use `key _ _ ?_ w w.2` and prove the remaining obligations. Establish `h3` using `K.mul_mem (K.mul_mem (pick_spec x hx) hc) (K.inv_mem (pick_spec _ hxc))`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Use `group`. Establish `hxc : ¬ S (x * c)` using `fun h => hx (by`. Use `S_right c⁻¹ (K.inv_mem hc) _ h` as an intermediate fact. Simplify using `using this)`.

Rewrite using `[F_neg w _ hxc, F_neg w _ hx]`. Establish `hfix' : ∀ (w : A), ∀ c ∈ K, ind H σ c ⟨F w, hlaw w⟩ = ⟨F w, hlaw w⟩` using `fun w c hc => Subtype.ext (funext fun x => hfix w c hc x)`. Establish `hsm : ∀ w : A, (⟨F w, hlaw w⟩ : indSpace H σ) ∈ smoothPart (ind H σ)` using `fun w => mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem) fun c hc => hfix' w c hc)`. Establish `hT : ∀ w : A, (⟨⟨F w, hlaw w⟩, hsm w⟩ : smoothPart (ind H σ)) ∈ fixed (smInd H σ) K`. Introduce `w c`.

Rewrite using `[MonoidHom.one_apply, Units.val_one, one_smul]`. Conclude with `Subtype.ext (hfix' w c c.2)`. Set `T : A →ₗ[ℂ] fixed (smInd H σ) K` to `{ toFun := fun w => ⟨⟨⟨F w, hlaw w⟩, hsm w⟩, hT w⟩ map_add' := fun a b => Subtype.ext (Subtype.ext (Subtype.ext (map_add F a b))) map_smul' := fun c a => Subtype.ext (Subtype.ext (Subtype.ext (map_smul F c a))) }`. Establish `hS1 : S 1` using `⟨1, by simp [K.one_mem]⟩`. Establish `hF1 : ∀ w : A, F w 1 = w`.

Introduce `w`. Rewrite using `[F_pos w 1 hS1]`. Use `(key 1 _ ?_ w w.2).trans (by simp)` and prove the remaining obligations. Establish `h3` using `K.inv_mem (pick_spec 1 hS1)`. Simplify using `using h3`.

Establish `hinj : Function.Injective T`. Introduce `a b hab`. Establish `h4 : F a = F b` using `congrArg (fun t : fixed (smInd H σ) K => t.1.1.1) hab`. Conclude with `Subtype.ext (by rw [← hF1 a, ← hF1 b, h4])`. Conclude with `Module.Finite.of_injective T hinj`.
-/
theorem finiteDimensional_of_smInd_fixed {G W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (H K : Subgroup G)
    (hK : IsOpen (K : Set G)) (σ : Representation ℂ H W) (A : Submodule ℂ W)
    (hA : ∀ c : H, (c : G) ∈ K → ∀ w ∈ A, σ c w = w)
    (hfd : FiniteDimensional ℂ (fixed (smInd H σ) K)) : FiniteDimensional ℂ A := by
  classical
  have key : ∀ p q : H, (p : G)⁻¹ * q ∈ K → ∀ w ∈ A, σ q w = σ p w := by
    intro p q hpq w hw
    have h1 : σ (p⁻¹ * q) w = w := hA _ (by simpa using hpq) w hw
    have h2 : q = p * (p⁻¹ * q) := by group
    calc σ q w = σ (p * (p⁻¹ * q)) w := by rw [← h2]
      _ = σ p (σ (p⁻¹ * q) w) := by rw [map_mul]; rfl
      _ = σ p w := by rw [h1]
  let S : G → Prop := fun x => ∃ p : H, (p : G)⁻¹ * x ∈ K
  let pick : G → H := fun x => if h : S x then h.choose else 1
  have pick_spec : ∀ x, S x → ((pick x : H) : G)⁻¹ * x ∈ K := by
    intro x h
    simp only [pick, dif_pos h]
    exact h.choose_spec
  let F : A →ₗ[ℂ] (G → W) := LinearMap.pi fun x =>
    if S x then (σ (pick x)).comp A.subtype else 0
  have F_pos : ∀ (w : A) x, S x → F w x = σ (pick x) w := by
    intro w x h
    simp [F, h]
  have F_neg : ∀ (w : A) x, ¬ S x → F w x = 0 := by
    intro w x h
    simp [F, h]
  have S_left : ∀ (q : H) x, S x → S (q * x) := by
    rintro q x ⟨p, hp⟩
    exact ⟨q * p, by simpa [mul_assoc] using hp⟩
  have S_right : ∀ c ∈ K, ∀ x, S x → S (x * c) := by
    rintro c hc x ⟨p, hp⟩
    exact ⟨p, by simpa [mul_assoc] using K.mul_mem hp hc⟩
  have hlaw : ∀ w : A, F w ∈ indSpace H σ := by
    intro w q x
    by_cases hx : S x
    · have hqx := S_left q x hx
      rw [F_pos w _ hqx, F_pos w _ hx, ← Module.End.mul_apply, ← map_mul]
      refine key _ _ ?_ w w.2
      have h3 := K.mul_mem (pick_spec x hx) (K.inv_mem (pick_spec _ hqx))
      convert h3 using 1
      simp only [Subgroup.coe_mul]
      group
    · have hqx : ¬ S (q * x) := fun h => hx (by
        have := S_left q⁻¹ _ h
        simpa using this)
      rw [F_neg w _ hqx, F_neg w _ hx, map_zero]
  have hfix : ∀ (w : A), ∀ c ∈ K, ∀ x, F w (x * c) = F w x := by
    intro w c hc x
    by_cases hx : S x
    · have hxc := S_right c hc x hx
      rw [F_pos w _ hxc, F_pos w _ hx]
      refine key _ _ ?_ w w.2
      have h3 := K.mul_mem (K.mul_mem (pick_spec x hx) hc) (K.inv_mem (pick_spec _ hxc))
      convert h3 using 1
      group
    · have hxc : ¬ S (x * c) := fun h => hx (by
        have := S_right c⁻¹ (K.inv_mem hc) _ h
        simpa using this)
      rw [F_neg w _ hxc, F_neg w _ hx]
  have hfix' : ∀ (w : A), ∀ c ∈ K, ind H σ c ⟨F w, hlaw w⟩ = ⟨F w, hlaw w⟩ :=
    fun w c hc => Subtype.ext (funext fun x => hfix w c hc x)
  have hsm : ∀ w : A, (⟨F w, hlaw w⟩ : indSpace H σ) ∈ smoothPart (ind H σ) := fun w =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem)
      fun c hc => hfix' w c hc)
  have hT : ∀ w : A, (⟨⟨F w, hlaw w⟩, hsm w⟩ : smoothPart (ind H σ)) ∈ fixed (smInd H σ) K := by
    intro w c
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact Subtype.ext (hfix' w c c.2)
  let T : A →ₗ[ℂ] fixed (smInd H σ) K :=
    { toFun := fun w => ⟨⟨⟨F w, hlaw w⟩, hsm w⟩, hT w⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (Subtype.ext (map_add F a b)))
      map_smul' := fun c a => Subtype.ext (Subtype.ext (Subtype.ext (map_smul F c a))) }
  have hS1 : S 1 := ⟨1, by simp [K.one_mem]⟩
  have hF1 : ∀ w : A, F w 1 = w := by
    intro w
    rw [F_pos w 1 hS1]
    refine (key 1 _ ?_ w w.2).trans (by simp)
    have h3 := K.inv_mem (pick_spec 1 hS1)
    simpa using h3
  have hinj : Function.Injective T := by
    intro a b hab
    have h4 : F a = F b := congrArg (fun t : fixed (smInd H σ) K => t.1.1.1) hab
    exact Subtype.ext (by rw [← hF1 a, ← hF1 b, h4])
  exact Module.Finite.of_injective T hinj

/- English proof (translation)
Introduce `k _ _ _ _ s d W _ _ ρ hρ hA`. Use `⟨hρ, fun L hLo _ => ?_⟩` and prove the remaining obligations. Set `δ` to `deltaHalf k fun a => Fin (d a)`. Set `L' : Subgroup (Levi k fun a => Fin (d a))` to `L ⊓ δ.ker`. Establish `hL' : IsOpen (L' : Set (Levi k fun a => Fin (d a)))` using `hLo.inter (isSmoothChar_deltaHalf k)`.

Establish `hpre` using `hL'.preimage (ProdIrr.continuous_leviProj (GlobalTheory.CompanionTheory.BZInd.stdE d))`. Take `⟨U, hU, hUe⟩` from `isOpen_induced_iff.1 hpre`. Establish `h1 : (1 : GL (Fin (∑ a, d a)) k) ∈ U`. Establish `h2 : (1 : parab k (GlobalTheory.CompanionTheory.BZInd.stdE d)) ∈ Subtype.val ⁻¹' U`. Rewrite using `[hUe]`.

Simplify using `using L'.one_mem`. Conclude with `h2`. Take `⟨m, -, hm⟩` from `(GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k (∑ a, d a)).mem_iff.1 (hU.mem_nhds h1)`. Establish `hKo` using `GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k (∑ a, d a) m`. Establish `hKc` using `GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k (∑ a, d a) m`.

Use `finiteDimensional_of_smInd_fixed (parab k (GlobalTheory.CompanionTheory.BZInd.stdE d)) (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (∑ a, d a) m) hKo ((twist ρ δ).comp (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d))) (fixed ρ L) ?_ (hA.2 _ hKo hKc)` and prove the remaining obligations. Introduce `c hc w hw`. Establish `hcL : leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c ∈ L'`. Establish `h2 : c ∈ Subtype.val ⁻¹' U` using `hm hc`. Rewrite `h2` using `[hUe]`.

Conclude with `h2`. Establish `hδ : δ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) = 1` using `MonoidHom.mem_ker.1 hcL.2`. Establish `hw'` using `hw ⟨_, hcL.1⟩`. Rewrite `hw'` using `[MonoidHom.one_apply, Units.val_one, one_smul]`. Use `show ((δ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) : ℂˣ) : ℂ) • ρ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) w = w`.

Rewrite using `[hδ, Units.val_one, one_smul]`. Conclude with `hw'`.
-/
theorem isAdmissible_of_parInd : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {s : ℕ} (d : Fin s → ℕ) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W),
    IsSmooth ρ → IsAdmissible (parInd (GlobalTheory.CompanionTheory.BZInd.stdE d) ρ) → IsAdmissible ρ := by
  intro k _ _ _ _ s d W _ _ ρ hρ hA
  refine ⟨hρ, fun L hLo _ => ?_⟩
  let δ := deltaHalf k fun a => Fin (d a)
  let L' : Subgroup (Levi k fun a => Fin (d a)) := L ⊓ δ.ker
  have hL' : IsOpen (L' : Set (Levi k fun a => Fin (d a))) :=
    hLo.inter (isSmoothChar_deltaHalf k)
  have hpre := hL'.preimage (ProdIrr.continuous_leviProj (GlobalTheory.CompanionTheory.BZInd.stdE d))
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hpre
  have h1 : (1 : GL (Fin (∑ a, d a)) k) ∈ U := by
    have h2 : (1 : parab k (GlobalTheory.CompanionTheory.BZInd.stdE d)) ∈ Subtype.val ⁻¹' U := by
      rw [hUe]
      simpa using L'.one_mem
    exact h2
  obtain ⟨m, -, hm⟩ :=
    (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k (∑ a, d a)).mem_iff.1 (hU.mem_nhds h1)
  have hKo := GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k (∑ a, d a) m
  have hKc := GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k (∑ a, d a) m
  refine finiteDimensional_of_smInd_fixed (parab k (GlobalTheory.CompanionTheory.BZInd.stdE d))
    (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (∑ a, d a) m) hKo
    ((twist ρ δ).comp (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d))) (fixed ρ L) ?_ (hA.2 _ hKo hKc)
  intro c hc w hw
  have hcL : leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c ∈ L' := by
    have h2 : c ∈ Subtype.val ⁻¹' U := hm hc
    rw [hUe] at h2
    exact h2
  have hδ : δ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) = 1 := MonoidHom.mem_ker.1 hcL.2
  have hw' := hw ⟨_, hcL.1⟩
  rw [MonoidHom.one_apply, Units.val_one, one_smul] at hw'
  show ((δ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) : ℂˣ) : ℂ) •
    ρ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) w = w
  rw [hδ, Units.val_one, one_smul]
  exact hw'

end GlobalTheory.CompanionTheory.LeviAdm
