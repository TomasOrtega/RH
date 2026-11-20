import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherent
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.QcqsPushforward

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Globalize

/- English proof (translation)
Take `⟨s, rfl⟩` from `hP`. Establish `h' : ∀ x ∈ s, ∃ k : ℕ, ∀ n, f ^ k • x ∈ N n` using `fun x hx => h x (Submodule.subset_span (Finset.mem_coe.2 hx))`. Use `choose! k hk using h'`. Use `⟨s.sup k, fun n x hx => ?_⟩` and prove the remaining obligations. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem y hy`. Establish `hy' : y ∈ s` using `Finset.mem_coe.1 hy`. Establish `e : f ^ s.sup k • y = f ^ (s.sup k - k y) • f ^ k y • y`. Rewrite using `[smul_smul, ← pow_add, Nat.sub_add_cancel (Finset.le_sup hy')]`. Rewrite using `[e]`.

Conclude with `(N n).smul_mem _ (hk y hy' n)`. Consider the case `zero => rw [smul_zero]`. Conclude with `(N n).zero_mem`. Consider the case `add y z _ _ hy hz => rw [smul_add]`. Conclude with `(N n).add_mem hy hz`.

Consider the case `smul r y _ hy => rw [smul_comm]`. Conclude with `(N n).smul_mem _ hy`.
-/
lemma exists_pow_smul_uniform {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (P : Submodule R M) (hP : P.FG) (N : ℕ → Submodule R M) (f : R)
    (h : ∀ x ∈ P, ∃ k : ℕ, ∀ n, f ^ k • x ∈ N n) :
    ∃ k : ℕ, ∀ n, ∀ x ∈ P, f ^ k • x ∈ N n := by
  classical
  obtain ⟨s, rfl⟩ := hP
  have h' : ∀ x ∈ s, ∃ k : ℕ, ∀ n, f ^ k • x ∈ N n :=
    fun x hx => h x (Submodule.subset_span (Finset.mem_coe.2 hx))
  choose! k hk using h'
  refine ⟨s.sup k, fun n x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ s := Finset.mem_coe.1 hy
    have e : f ^ s.sup k • y = f ^ (s.sup k - k y) • f ^ k y • y := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel (Finset.le_sup hy')]
    rw [e]
    exact (N n).smul_mem _ (hk y hy' n)
  | zero => rw [smul_zero]; exact (N n).zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact (N n).add_mem hy hz
  | smul r y _ hy => rw [smul_comm]; exact (N n).smul_mem _ hy

variable {X : Scheme.{0}}

def killIdeal {E : X.Modules} (D : Subobject E) (S : ℕ → Subobject E) (V : X.Opens) :
    Ideal Γ(X, V) :=
  ⨅ n, (secsSub (S n) V).colon (secs D V)

/- English proof (translation)
Simplify using `only [killIdeal, Submodule.mem_iInf, Submodule.mem_colon]`. Both sides reduce to the same expression.
-/
lemma mem_killIdeal {E : X.Modules} {D : Subobject E} {S : ℕ → Subobject E} {V : X.Opens}
    {a : Γ(X, V)} : a ∈ killIdeal D S V ↔ ∀ n, ∀ x ∈ secs D V, a • x ∈ secs (S n) V := by
  simp only [killIdeal, Submodule.mem_iInf, Submodule.mem_colon]
  rfl

/- English proof (translation)
Use `haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V`. Establish `hfin : Module.Finite Γ(X, V) Γ((D : X.Modules), V)` using `(isCoherent_subobject hE D hD).2 V V.2`. Set `φ : Γ((D : X.Modules), V) →ₗ[Γ(X, V)] Γ(E, V)` to `{ toFun := D.arrow.app V map_add' := map_add _ map_smul' := Scheme.Modules.Hom.app_smul _ }`. Establish `hr : secsSub D V = LinearMap.range φ` using `Submodule.ext fun _ => Iff.rfl`. Establish `hP : (secsSub D V).FG`.

Rewrite using `[hr, LinearMap.range_eq_map]`. Conclude with `(Module.Finite.fg_top).map φ`. Establish `hrad : J₀.ideal V ≤ (killIdeal D S V).radical`. Introduce `f hf`. Take `⟨k, hk⟩` from `exists_pow_smul_uniform (secsSub D V) hP (fun n => secsSub (S n) V) f (fun x hx => h f hf x hx)`.

Conclude with `⟨k, mem_killIdeal.2 fun n x hx => hk n x hx⟩`. Conclude with `Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)`.
-/
theorem exists_pow_le_killIdeal [IsLocallyNoetherian X] {E : X.Modules} (hE : IsCoherent E)
    (D : Subobject E) (hD : (D : X.Modules).IsQuasicoherent) (S : ℕ → Subobject E)
    (J₀ : X.IdealSheafData) (V : X.affineOpens)
    (h : ∀ f ∈ J₀.ideal V, ∀ x ∈ secs D V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V) :
    ∃ m : ℕ, J₀.ideal V ^ m ≤ killIdeal D S V := by
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  have hfin : Module.Finite Γ(X, V) Γ((D : X.Modules), V) :=
    (isCoherent_subobject hE D hD).2 V V.2
  let φ : Γ((D : X.Modules), V) →ₗ[Γ(X, V)] Γ(E, V) :=
    { toFun := D.arrow.app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  have hr : secsSub D V = LinearMap.range φ := Submodule.ext fun _ => Iff.rfl
  have hP : (secsSub D V).FG := by
    rw [hr, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map φ
  have hrad : J₀.ideal V ≤ (killIdeal D S V).radical := by
    intro f hf
    obtain ⟨k, hk⟩ := exists_pow_smul_uniform (secsSub D V) hP (fun n => secsSub (S n) V) f
      (fun x hx => h f hf x hx)
    exact ⟨k, mem_killIdeal.2 fun n x hx => hk n x hx⟩
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

end GlobalTheory.CompanionTheory.GE.Globalize

namespace GlobalTheory.CompanionTheory.GE.Globalize

variable {X : Scheme.{0}}

/- English proof (translation)
Establish `hmap : Ideal.map (resO (X.basicOpen_le g)) (J₀.ideal V ^ m) = J₀.ideal (X.affineBasicOpen g) ^ m`. Rewrite using `[Ideal.map_pow, J₀.map_ideal_basicOpen]`. Both sides reduce to the same expression. Introduce `a ha`. Rewrite `ha` using `[← hmap]`.

Use `(Ideal.map_le_iff_le_comap.2 ?_ : Ideal.map (resO (X.basicOpen_le g)) (J₀.ideal V ^ m) ≤ killIdeal D S (X.basicOpen g)) ha` and prove the remaining obligations. Introduce `r hr`. Rewrite using `[Ideal.mem_comap]`. Use `mem_killIdeal.2 fun n x hx => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hx`.

Take `⟨e, y', hy'⟩` from `qcoh_exists_res_eq (D : X.Modules) V.2 g y`. Take `⟨z, hz⟩` from `mem_killIdeal.1 (hV hr) n _ ⟨y', rfl⟩`. Establish `key : resO (X.basicOpen_le g) g ^ e • (resO (X.basicOpen_le g) r • D.arrow.app _ y) ∈ secs (S n) (X.basicOpen g)`. Use `⟨resF _ (X.basicOpen_le g) z, ?_⟩` and prove the remaining obligations. Rewrite using `[← resF_app, hz, resF_smul, resF_app, hy', Scheme.Modules.Hom.app_smul, smul_comm]`.

Take `⟨u, hu⟩ : IsUnit (resO (X.basicOpen_le g) g)` from `X.toRingedSpace.isUnit_res_basicOpen g`. Establish `e2 : resO (X.basicOpen_le g) r • D.arrow.app _ y = ((u⁻¹ : (Γ(X, X.basicOpen g))ˣ) : Γ(X, X.basicOpen g)) ^ e • (resO (X.basicOpen_le g) g ^ e • (resO (X.basicOpen_le g) r • D.arrow.app _ y))`. Rewrite using `[smul_smul, ← mul_pow, ← hu, Units.inv_mul, one_pow, one_smul]`. Rewrite using `[e2]`. Conclude with `(secsSub (S n) (X.basicOpen g)).smul_mem _ key`.
-/
theorem pow_le_killIdeal_basicOpen {E : X.Modules} (D : Subobject E)
    [(D : X.Modules).IsQuasicoherent] (S : ℕ → Subobject E) (J₀ : X.IdealSheafData)
    (V : X.affineOpens) (m : ℕ) (hV : J₀.ideal V ^ m ≤ killIdeal D S V) (g : Γ(X, V)) :
    J₀.ideal (X.affineBasicOpen g) ^ m ≤ killIdeal D S (X.basicOpen g) := by
  have hmap : Ideal.map (resO (X.basicOpen_le g)) (J₀.ideal V ^ m) =
      J₀.ideal (X.affineBasicOpen g) ^ m := by
    rw [Ideal.map_pow, J₀.map_ideal_basicOpen]
    rfl
  intro a ha
  rw [← hmap] at ha
  refine (Ideal.map_le_iff_le_comap.2 ?_ : Ideal.map (resO (X.basicOpen_le g)) (J₀.ideal V ^ m) ≤
    killIdeal D S (X.basicOpen g)) ha
  intro r hr
  rw [Ideal.mem_comap]
  refine mem_killIdeal.2 fun n x hx => ?_
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨e, y', hy'⟩ := qcoh_exists_res_eq (D : X.Modules) V.2 g y
  obtain ⟨z, hz⟩ := mem_killIdeal.1 (hV hr) n _ ⟨y', rfl⟩
  have key : resO (X.basicOpen_le g) g ^ e • (resO (X.basicOpen_le g) r • D.arrow.app _ y) ∈
      secs (S n) (X.basicOpen g) := by
    refine ⟨resF _ (X.basicOpen_le g) z, ?_⟩
    rw [← resF_app, hz, resF_smul, resF_app, hy', Scheme.Modules.Hom.app_smul, smul_comm]
  obtain ⟨u, hu⟩ : IsUnit (resO (X.basicOpen_le g) g) := X.toRingedSpace.isUnit_res_basicOpen g
  have e2 : resO (X.basicOpen_le g) r • D.arrow.app _ y =
      ((u⁻¹ : (Γ(X, X.basicOpen g))ˣ) : Γ(X, X.basicOpen g)) ^ e •
        (resO (X.basicOpen_le g) g ^ e • (resO (X.basicOpen_le g) r • D.arrow.app _ y)) := by
    rw [smul_smul, ← mul_pow, ← hu, Units.inv_mul, one_pow, one_smul]
  rw [e2]
  exact (secsSub (S n) (X.basicOpen g)).smul_mem _ key

/- English proof (translation)
Use `choose W hpW hWU hW using h`. Establish `h0 : (cokernel.π T.arrow).app U x = 0`. Use `eq_of_forall_resF (cokernel T.arrow) (fun p : (U : X.Opens) => (W p.1 p.2 : X.Opens)) (fun p => hWU p.1 p.2) ?_ _ 0 ?_` and prove the remaining obligations. Introduce `p hp`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp⟩, hpW p hp⟩`.

Introduce `p`. Take `⟨z, hz⟩` from `hW p.1 p.2`. Rewrite using `[resF_app, ← hz, map_zero, (GlobalTheory.QCoh.exact_cokernel_π_app T.arrow (W p.1 p.2).2).apply_apply_eq_zero z]`. Conclude with `(GlobalTheory.QCoh.exact_cokernel_π_app T.arrow U.2 x).1 h0`.
-/
theorem mem_secs_of_local {E : X.Modules} [E.IsQuasicoherent] (T : Subobject E)
    [(T : X.Modules).IsQuasicoherent] (U : X.affineOpens) (x : Γ(E, U))
    (h : ∀ p ∈ (U : X.Opens), ∃ W : X.affineOpens, p ∈ (W : X.Opens) ∧
      ∃ hW : (W : X.Opens) ≤ U, resF E hW x ∈ secs T W) :
    x ∈ secs T U := by
  choose W hpW hWU hW using h
  have h0 : (cokernel.π T.arrow).app U x = 0 := by
    refine eq_of_forall_resF (cokernel T.arrow) (fun p : (U : X.Opens) => (W p.1 p.2 : X.Opens))
      (fun p => hWU p.1 p.2) ?_ _ 0 ?_
    · intro p hp
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp⟩, hpW p hp⟩
    · intro p
      obtain ⟨z, hz⟩ := hW p.1 p.2
      rw [resF_app, ← hz, map_zero, (GlobalTheory.QCoh.exact_cokernel_π_app T.arrow (W p.1 p.2).2).apply_apply_eq_zero z]
  exact (GlobalTheory.QCoh.exact_cokernel_π_app T.arrow U.2 x).1 h0

end GlobalTheory.CompanionTheory.GE.Globalize

namespace GlobalTheory.CompanionTheory.GE.Globalize

/- English proof (translation)
Introduce `X _ _ E hE D hD S hS J₀ hJ`. Use `choose mV hmV using fun V : X.affineOpens => exists_pow_le_killIdeal hE D hD S J₀ V (hJ V)`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun V : X.affineOpens => ((V : X.Opens) : Set X)) (fun V => (V : X.Opens).isOpen) (by`. Introduce `p _`. Choose the witnesses or unpack the hypotheses as in `⟨V, hV⟩ : ∃ V : X.affineOpens, p ∈ (V : X.Opens) := by`.

Take `⟨V, hV, hpV, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show p ∈ (⊤ : X.Opens) from trivial)`. Conclude with `⟨⟨V, hV⟩, hpV⟩`. Conclude with `Set.mem_iUnion.2 ⟨V, hV⟩)`. Use `⟨t.sup mV, fun n U a ha x hx => ?_⟩` and prove the remaining obligations. Use `haveI : E.IsQuasicoherent := hE.1`.

Use `haveI : (D : X.Modules).IsQuasicoherent := hD`. Use `haveI := hS n`. Use `mem_secs_of_local (S n) U (a • x) fun p hpU => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨V, hVt, hpV⟩ : ∃ V ∈ t, p ∈ ((V : X.Opens) : Set X) := by`. Simplify using `using ht (Set.mem_univ p)`.

Take `⟨f, g, hfg, hpf⟩` from `exists_basicOpen_le_affine_inter U.2 V.2 p ⟨hpU, hpV⟩`. Establish `hWU : X.basicOpen g ≤ (U : X.Opens)` using `hfg ▸ X.basicOpen_le f`. Use `⟨X.affineBasicOpen g, (show p ∈ X.basicOpen g from hfg ▸ hpf), hWU, ?_⟩` and prove the remaining obligations. Establish `hVm : J₀.ideal V ^ t.sup mV ≤ killIdeal D S V` using `(Ideal.pow_le_pow_right (Finset.le_sup hVt)).trans (hmV V)`. Establish `hk` using `pow_le_killIdeal_basicOpen D S J₀ V _ hVm g`.

Establish `hWU' : X.affineBasicOpen g ≤ U` using `hWU`. Establish `ha' : resO hWU a ∈ J₀.ideal (X.affineBasicOpen g) ^ t.sup mV`. Use `Ideal.mem_map_of_mem (resO hWU) (show a ∈ J₀.ideal U ^ t.sup mV from ha)` as an intermediate fact. Rewrite `this` using `[Ideal.map_pow]`. Conclude with `(J₀.map_ideal hWU') ▸ this`.

Take `⟨y, rfl⟩` from `hx`. Establish `e3` using `resF_smul E hWU a (D.arrow.app U y)`. Use `erw [e3, resF_app]`. Conclude with `mem_killIdeal.1 (hk ha') n _ ⟨_, rfl⟩`.
-/
theorem exists_uniform_pow_kills : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] [CompactSpace X]
    {E : X.Modules}, IsCoherent E → ∀ (D : Subobject E), (D : X.Modules).IsQuasicoherent →
    ∀ (S : ℕ → Subobject E), (∀ n, (S n : X.Modules).IsQuasicoherent) →
    ∀ J₀ : X.IdealSheafData, (∀ (V : X.affineOpens) (f : Γ(X, V)), f ∈ J₀.ideal V →
      ∀ x ∈ secs D V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V) →
    ∃ m : ℕ, ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ (powIdeal J₀ m).ideal U →
      ∀ x ∈ secs D U, a • x ∈ secs (S n) U := by
  intro X _ _ E hE D hD S hS J₀ hJ
  choose mV hmV using fun V : X.affineOpens => exists_pow_le_killIdeal hE D hD S J₀ V (hJ V)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens => ((V : X.Opens) : Set X))
    (fun V => (V : X.Opens).isOpen) (by
      intro p _
      obtain ⟨V, hV⟩ : ∃ V : X.affineOpens, p ∈ (V : X.Opens) := by
        obtain ⟨V, hV, hpV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
          (show p ∈ (⊤ : X.Opens) from trivial)
        exact ⟨⟨V, hV⟩, hpV⟩
      exact Set.mem_iUnion.2 ⟨V, hV⟩)
  refine ⟨t.sup mV, fun n U a ha x hx => ?_⟩
  haveI : E.IsQuasicoherent := hE.1
  haveI : (D : X.Modules).IsQuasicoherent := hD
  haveI := hS n
  refine mem_secs_of_local (S n) U (a • x) fun p hpU => ?_
  obtain ⟨V, hVt, hpV⟩ : ∃ V ∈ t, p ∈ ((V : X.Opens) : Set X) := by
    simpa using ht (Set.mem_univ p)
  obtain ⟨f, g, hfg, hpf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 p ⟨hpU, hpV⟩
  have hWU : X.basicOpen g ≤ (U : X.Opens) := hfg ▸ X.basicOpen_le f
  refine ⟨X.affineBasicOpen g, (show p ∈ X.basicOpen g from hfg ▸ hpf), hWU, ?_⟩
  have hVm : J₀.ideal V ^ t.sup mV ≤ killIdeal D S V :=
    (Ideal.pow_le_pow_right (Finset.le_sup hVt)).trans (hmV V)
  have hk := pow_le_killIdeal_basicOpen D S J₀ V _ hVm g
  have hWU' : X.affineBasicOpen g ≤ U := hWU
  have ha' : resO hWU a ∈ J₀.ideal (X.affineBasicOpen g) ^ t.sup mV := by
    have := Ideal.mem_map_of_mem (resO hWU) (show a ∈ J₀.ideal U ^ t.sup mV from ha)
    rw [Ideal.map_pow] at this
    exact (J₀.map_ideal hWU') ▸ this
  obtain ⟨y, rfl⟩ := hx
  have e3 := resF_smul E hWU a (D.arrow.app U y)
  erw [e3, resF_app]
  exact mem_killIdeal.1 (hk ha') n _ ⟨_, rfl⟩

end GlobalTheory.CompanionTheory.GE.Globalize
