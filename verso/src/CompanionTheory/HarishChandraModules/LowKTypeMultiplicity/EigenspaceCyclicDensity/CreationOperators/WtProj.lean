import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LKWtProj

open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KRel KUnit KStab)

/- English proof (translation)
Proceed by induction on `ht using Submodule.iSup_induction' with`. Consider the case `mem μ x hx`. Rewrite `hx` using `[Module.End.mem_eigenspace_iff]`. Distinguish the cases in `h : μ = τ`. Substitute `h` using the available equality.

Conclude with `⟨1, fun G _ => Commute.one_left G, fun W _ x hx => hx, fun y _ => rfl, hx⟩`. Use `⟨(τ - μ)⁻¹ • (F - μ • 1), fun G hG => ?_, fun W hW y hy => ?_, fun y hy => ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hG.sub_left ((Commute.one_left G).smul_left μ)).smul_left _`. Simplify using `using W.smul_mem _ (W.sub_mem (hW y hy) (W.smul_mem μ hy))`. Establish `h' : τ - μ ≠ 0` using `sub_ne_zero.2 (Ne.symm h)`.

Simplify using `only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, hy, ← sub_smul, smul_smul, inv_mul_cancel₀ h', one_smul]`. Simplify using `[hx]`. Consider the case `zero => exact ⟨1, fun G _ => Commute.one_left G, fun W _ x hx => hx, fun y _ => rfl, by simp⟩`. Consider the case `add x y _ _ ihx ihy`. Take `⟨P, hP1, hP2, hP3, hP4⟩` from `ihx`.

Take `⟨Q, hQ1, hQ2, hQ3, hQ4⟩` from `ihy`. Establish `hPQ : Commute P Q` using `hP1 Q (hQ1 F (Commute.refl F)).symm`. Use `⟨P * Q, fun G hG => (hP1 G hG).mul_left (hQ1 G hG), fun W hW z hz => hP2 W hW _ (hQ2 W hW z hz), fun z hz => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, hQ3 z hz, hP3 z hz]`. Establish `h1 : (P * Q) x = P x` using `by rw [hPQ.eq, Module.End.mul_apply, hQ3 _ hP4]`.

Establish `h2 : (P * Q) y = Q y` using `by rw [Module.End.mul_apply, hP3 _ hQ4]`. Rewrite using `[map_add, h1, h2, map_add, hP4, hQ4, smul_add]`.
-/
theorem exists_proj {M : Type} [AddCommGroup M] [Module ℂ M] (F : Module.End ℂ M) (τ : ℂ) (t : M)
    (ht : t ∈ ⨆ μ : ℂ, F.eigenspace μ) :
    ∃ P : Module.End ℂ M, (∀ G, Commute F G → Commute P G) ∧
      (∀ W : Submodule ℂ M, (∀ x ∈ W, F x ∈ W) → ∀ x ∈ W, P x ∈ W) ∧
      (∀ y, F y = τ • y → P y = y) ∧ F (P t) = τ • P t := by
  induction ht using Submodule.iSup_induction' with
  | mem μ x hx =>
    rw [Module.End.mem_eigenspace_iff] at hx
    by_cases h : μ = τ
    · subst h
      exact ⟨1, fun G _ => Commute.one_left G, fun W _ x hx => hx, fun y _ => rfl, hx⟩
    · refine ⟨(τ - μ)⁻¹ • (F - μ • 1), fun G hG => ?_, fun W hW y hy => ?_, fun y hy => ?_, ?_⟩
      · exact (hG.sub_left ((Commute.one_left G).smul_left μ)).smul_left _
      · simpa using W.smul_mem _ (W.sub_mem (hW y hy) (W.smul_mem μ hy))
      · have h' : τ - μ ≠ 0 := sub_ne_zero.2 (Ne.symm h)
        simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, hy, ← sub_smul, smul_smul,
          inv_mul_cancel₀ h', one_smul]
      · simp [hx]
  | zero => exact ⟨1, fun G _ => Commute.one_left G, fun W _ x hx => hx, fun y _ => rfl, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨P, hP1, hP2, hP3, hP4⟩ := ihx
    obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := ihy
    have hPQ : Commute P Q := hP1 Q (hQ1 F (Commute.refl F)).symm
    refine ⟨P * Q, fun G hG => (hP1 G hG).mul_left (hQ1 G hG), fun W hW z hz => hP2 W hW _ (hQ2 W hW z hz),
      fun z hz => ?_, ?_⟩
    · rw [Module.End.mul_apply, hQ3 z hz, hP3 z hz]
    · have h1 : (P * Q) x = P x := by rw [hPQ.eq, Module.End.mul_apply, hQ3 _ hP4]
      have h2 : (P * Q) y = Q y := by rw [Module.End.mul_apply, hP3 _ hQ4]
      rw [map_add, h1, h2, map_add, hP4, hQ4, smul_add]

/- English proof (translation)
Establish `hs : (T.restrict hS).IsSymmetric` using `hT.restrict_invariant hS`. Establish `htop : (⨆ μ : ℂ, Module.End.eigenspace (T.restrict hS) μ) = ⊤` using `Submodule.orthogonal_eq_bot_iff.1 hs.orthogonalComplement_iSup_eigenspaces_eq_bot`. Establish `hle : ((⨆ μ : ℂ, Module.End.eigenspace (T.restrict hS) μ).map S.subtype) ≤ ⨆ μ : ℂ, T.eigenspace μ`. Rewrite using `[Submodule.map_iSup]`. Use `iSup_mono fun μ => ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `hy'` using `Module.End.mem_eigenspace_iff.1 hy`. Rewrite using `[Module.End.mem_eigenspace_iff]`. Conclude with `congrArg Subtype.val hy'`. Conclude with `hle ⟨⟨x, hx⟩, by rw [htop]; trivial, rfl⟩`.
-/
theorem mem_iSup_eigenspace {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (T : Module.End ℂ V)
    (hT : T.IsSymmetric) (S : Submodule ℂ V) [FiniteDimensional ℂ S] (hS : ∀ v ∈ S, T v ∈ S) (x : V) (hx : x ∈ S) :
    x ∈ ⨆ μ : ℂ, T.eigenspace μ := by
  have hs : (T.restrict hS).IsSymmetric := hT.restrict_invariant hS
  have htop : (⨆ μ : ℂ, Module.End.eigenspace (T.restrict hS) μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.1 hs.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hle : ((⨆ μ : ℂ, Module.End.eigenspace (T.restrict hS) μ).map S.subtype) ≤ ⨆ μ : ℂ, T.eigenspace μ := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun μ => ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' := Module.End.mem_eigenspace_iff.1 hy
    rw [Module.End.mem_eigenspace_iff]
    exact congrArg Subtype.val hy'
  exact hle ⟨⟨x, hx⟩, by rw [htop]; trivial, rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Ft_apply {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) (x : Cn n V) (A : Finset (Pos n)) :
    Ft ε E c x A = E c c (x A) + (wt (A.filter (cpt ε)) c : ℂ) • x A := rfl

/- English proof (translation)
Rewrite using `[← Finset.univ_sum_single t]`. Use `Submodule.sum_mem _ fun A _ => ?_` and prove the remaining obligations. Establish `hle : (⨆ μ : ℂ, (E c c).eigenspace μ).map (LinearMap.single ℂ (fun _ : Finset (Pos n) => V) A) ≤ ⨆ μ : ℂ, (Ft ε E c).eigenspace μ`. Rewrite using `[Submodule.map_iSup]`. Use `iSup_le fun μ => le_trans ?_ (le_iSup _ (μ + (wt (A.filter (cpt ε)) c : ℂ)))` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `hy'` using `Module.End.mem_eigenspace_iff.1 hy`. Rewrite using `[Module.End.mem_eigenspace_iff]`. Use function extensionality and compare the values at `B`. Rewrite using `[Ft_apply]`.

Distinguish the cases in `hB : B = A`. Substitute `hB` using the available equality. Simplify using `[hy', add_smul]`. Simplify using `[Pi.single_eq_of_ne hB]`. Conclude with `hle ⟨t A, h _, rfl⟩`.
-/
theorem chain_mem_iSup {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) (h : ∀ v : V, v ∈ ⨆ μ : ℂ, (E c c).eigenspace μ)
    (t : Cn n V) : t ∈ ⨆ μ : ℂ, (Ft ε E c).eigenspace μ := by
  classical
  rw [← Finset.univ_sum_single t]
  refine Submodule.sum_mem _ fun A _ => ?_
  have hle : (⨆ μ : ℂ, (E c c).eigenspace μ).map (LinearMap.single ℂ (fun _ : Finset (Pos n) => V) A) ≤
      ⨆ μ : ℂ, (Ft ε E c).eigenspace μ := by
    rw [Submodule.map_iSup]
    refine iSup_le fun μ => le_trans ?_ (le_iSup _ (μ + (wt (A.filter (cpt ε)) c : ℂ)))
    rintro _ ⟨y, hy, rfl⟩
    have hy' := Module.End.mem_eigenspace_iff.1 hy
    rw [Module.End.mem_eigenspace_iff]
    funext B
    rw [Ft_apply]
    by_cases hB : B = A
    · subst hB
      simp [hy', add_smul]
    · simp [Pi.single_eq_of_ne hB]
  exact hle ⟨t A, h _, rfl⟩

/- English proof (translation)
Establish `h : E c c * E d d = E d d * E c c`. Use `hE c c d d rfl rfl` as an intermediate fact. Distinguish the cases in `hcd : c = d`. Substitute `hcd` using the available equality. Both sides reduce to the same expression.

Rewrite `this` using `[if_neg hcd, if_neg (Ne.symm hcd), sub_zero, sub_eq_zero]`. Conclude with `this`. Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Establish `h' : E c c (E d d (x A)) = E d d (E c c (x A))` using `LinearMap.congr_fun h (x A)`. Simplify using `only [Module.End.mul_apply, Ft_apply, map_add, map_smul, h', smul_add, smul_smul, mul_comm (wt (A.filter (cpt ε₀)) c : ℂ)]`.

Normalize the expressions using the abelian group laws.
-/
theorem Ft_commute {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε₀ ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hE : KRel ε E) (c d : Fin n) : Commute (Ft ε₀ E c) (Ft ε₀ E d) := by
  have h : E c c * E d d = E d d * E c c := by
    have := hE c c d d rfl rfl
    by_cases hcd : c = d
    · subst hcd; rfl
    · rw [if_neg hcd, if_neg (Ne.symm hcd), sub_zero, sub_eq_zero] at this
      exact this
  refine LinearMap.ext fun x => funext fun A => ?_
  have h' : E c c (E d d (x A)) = E d d (E c c (x A)) := LinearMap.congr_fun h (x A)
  simp only [Module.End.mul_apply, Ft_apply, map_add, map_smul, h', smul_add, smul_smul,
    mul_comm (wt (A.filter (cpt ε₀)) c : ℂ)]
  abel

/- English proof (translation)
Introduce `n ε₀ ε V _ _ E hE hU hL D hD τ t ht`. Establish `hdiag : ∀ c (x : Cn n V), x ∈ ⨆ μ : ℂ, (Ft ε₀ E c).eigenspace μ` using `fun c => chain_mem_iSup ε₀ E c fun v => by`. Take `⟨S, hS, hst, hv⟩` from `hL v`. Conclude with `mem_iSup_eigenspace (E c c) (fun x y => hU c c rfl x y) S (hst c c rfl) v hv`. Set `W : Submodule ℂ (Cn n V)` to `{ carrier := {x | ∀ A, t A = 0 → x A = 0} add_mem' := fun {a b} ha hb A hA => by simp [ha A hA, hb A hA] zero_mem' := fun A _ => rfl smul_mem' := fun c a ha A hA => by simp [ha A hA] }`.

Establish `hW : ∀ c, ∀ x ∈ W, Ft ε₀ E c x ∈ W` using `fun c x hx A hA => by`. Rewrite using `[Ft_apply, hx A hA]`. Simplify using the standard rewrite rules. Establish `key : ∀ s : Finset (Fin n), ∃ t' : Cn n V, (∀ c ∈ s, Ft ε₀ E c t' = (τ c : ℂ) • t') ∧ D t' = D t ∧ t' ∈ W`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨t, by simp, rfl, fun A hA => hA⟩`. Consider the case `insert c s _ ih`. Take `⟨u, hu1, hu2, hu3⟩` from `ih`. Take `⟨P, hP1, hP2, hP3, hP4⟩` from `exists_proj (Ft ε₀ E c) (τ c) u (hdiag c u)`.

Use `⟨P u, fun d hd => ?_, ?_, hP2 W (hW c) u hu3⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hd with rfl | hd` into its components or cases. Conclude with `hP4`. Use `LinearMap.congr_fun (hP1 _ (Ft_commute ε₀ ε E hE c d)).eq u` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`.

Rewrite using `[← this, hu1 d hd, map_smul]`. Use `LinearMap.congr_fun (hP1 _ (hD c)).eq u` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[← this, hu2, hP3 _ (ht c)]`. Take `⟨t', h1, h2, h3⟩` from `key univ`.

Conclude with `⟨t', fun c => h1 c (mem_univ c), h2, h3⟩`.
-/
theorem wtProj : CompanionTheory.D.LK.WtProj := by
  intro n ε₀ ε V _ _ E hE hU hL D hD τ t ht
  have hdiag : ∀ c (x : Cn n V), x ∈ ⨆ μ : ℂ, (Ft ε₀ E c).eigenspace μ := fun c =>
    chain_mem_iSup ε₀ E c fun v => by
      obtain ⟨S, hS, hst, hv⟩ := hL v
      exact mem_iSup_eigenspace (E c c) (fun x y => hU c c rfl x y) S (hst c c rfl) v hv
  let W : Submodule ℂ (Cn n V) :=
    { carrier := {x | ∀ A, t A = 0 → x A = 0}
      add_mem' := fun {a b} ha hb A hA => by simp [ha A hA, hb A hA]
      zero_mem' := fun A _ => rfl
      smul_mem' := fun c a ha A hA => by simp [ha A hA] }
  have hW : ∀ c, ∀ x ∈ W, Ft ε₀ E c x ∈ W := fun c x hx A hA => by
    rw [Ft_apply, hx A hA]; simp
  have key : ∀ s : Finset (Fin n), ∃ t' : Cn n V, (∀ c ∈ s, Ft ε₀ E c t' = (τ c : ℂ) • t') ∧ D t' = D t ∧
      t' ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨t, by simp, rfl, fun A hA => hA⟩
    | insert c s _ ih =>
      obtain ⟨u, hu1, hu2, hu3⟩ := ih
      obtain ⟨P, hP1, hP2, hP3, hP4⟩ := exists_proj (Ft ε₀ E c) (τ c) u (hdiag c u)
      refine ⟨P u, fun d hd => ?_, ?_, hP2 W (hW c) u hu3⟩
      · rcases Finset.mem_insert.1 hd with rfl | hd
        · exact hP4
        · have := LinearMap.congr_fun (hP1 _ (Ft_commute ε₀ ε E hE c d)).eq u
          simp only [Module.End.mul_apply] at this
          rw [← this, hu1 d hd, map_smul]
      · have := LinearMap.congr_fun (hP1 _ (hD c)).eq u
        simp only [Module.End.mul_apply] at this
        rw [← this, hu2, hP3 _ (ht c)]
  obtain ⟨t', h1, h2, h3⟩ := key univ
  exact ⟨t', fun c => h1 c (mem_univ c), h2, h3⟩

end GlobalTheory.CompanionTheory.LKWtProj
