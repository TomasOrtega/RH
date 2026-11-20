import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenDirected
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CycZConjGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RestrMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.IsCMOfConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base

namespace UpperTheory.V.Kum

section Lim

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

omit [IsAlgClosure F Ω] in
/- English proof (translation)
Introduce `g hg`. Simplify using `only [levU, Subgroup.mem_inf, Subgroup.mem_comap, KStar.TotallyRealRoots.mem_princ] at hg ⊢`. Conclude with `⟨hg.1, (pow_dvd_pow _ h).trans hg.2⟩`.
-/
theorem levU_anti (U : Subgroup (G F Ω)) {m n : ℕ} (h : m ≤ n) : levU l U n ≤ levU l U m := by
  intro g hg
  simp only [levU, Subgroup.mem_inf, Subgroup.mem_comap, KStar.TotallyRealRoots.mem_princ] at hg ⊢
  exact ⟨hg.1, (pow_dvd_pow _ h).trans hg.2⟩

omit [IsAlgClosure F Ω] in

/- English proof (translation)
Use `lenDirected R _ W (fun n => (P n).map (restr R M (cycU_le_levU l U n))) Bd ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `m n h _ ⟨ψ, hψ, rfl⟩`. Conclude with `⟨_, hP m n h ⟨ψ, hψ, rfl⟩, rfl⟩`. Introduce `φ hφ`. Take `⟨n, ψ, hψ, rfl⟩` from `hW φ hφ`.

Conclude with `Submodule.mem_iSup_of_mem n ⟨ψ, hψ, rfl⟩`. Introduce `n₀`. Take `⟨n, h, hn⟩` from `hB n₀`. Conclude with `⟨n, h, (Module.length_le_of_surjective _ (LinearMap.submoduleMap_surjective _ _)).trans hn⟩`.
-/
theorem len_le_of_layers (U : Subgroup (G F Ω)) (W : Submodule R (cycU l U → M)) (P : ∀ n, Submodule R (levU l U n → M))
    (hP : ∀ m n (h : m ≤ n), (P m).map (restr R M (levU_anti U h)) ≤ P n)
    (hW : ∀ φ ∈ W, ∃ n, ∃ ψ ∈ P n, restr R M (cycU_le_levU l U n) ψ = φ) (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length R (P n) ≤ Bd) : Module.length R W ≤ Bd := by
  refine lenDirected R _ W (fun n => (P n).map (restr R M (cycU_le_levU l U n))) Bd ?_ ?_ ?_
  · rintro m n h _ ⟨ψ, hψ, rfl⟩
    exact ⟨_, hP m n h ⟨ψ, hψ, rfl⟩, rfl⟩
  · intro φ hφ
    obtain ⟨n, ψ, hψ, rfl⟩ := hW φ hφ
    exact Submodule.mem_iSup_of_mem n ⟨ψ, hψ, rfl⟩
  · intro n₀
    obtain ⟨n, h, hn⟩ := hB n₀
    exact ⟨n, h, (Module.length_le_of_surjective _ (LinearMap.submoduleMap_surjective _ _)).trans hn⟩

/- English proof (translation)
Use `(fnCyc F Ω l n).1` as an intermediate fact. Rewrite using `[galOfCyc F Ω l n F (Fn F Ω l n), galOf_self]`.
-/
theorem galOf_Fn (n : ℕ) : galOf F (Fn F Ω l n) Ω = Un F Ω l n := by
  have := (fnCyc F Ω l n).1
  rw [galOfCyc F Ω l n F (Fn F Ω l n), galOf_self]

omit [NumberField F] in
/- English proof (translation)
The claim follows from `Module.length_le_of_surjective _ (LinearMap.submoduleMap_surjective f N)`.
-/
theorem length_map_le {X Y : Type} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y)
    (N : Submodule R X) : Module.length R (N.map f) ≤ Module.length R N :=
  Module.length_le_of_surjective _ (LinearMap.submoduleMap_surjective f N)

/- English proof (translation)
Rewrite using `[Module.length_eq_add_of_exact (LinearMap.ker (f.submoduleMap N)).subtype (f.submoduleMap N) (Submodule.subtype_injective _) (LinearMap.submoduleMap_surjective f N) (LinearMap.exact_subtype_ker_map _), add_comm]`. Use `add_le_add le_rfl (Module.length_le_of_injective (LinearMap.codRestrict _ (N.subtype.comp (LinearMap.ker (f.submoduleMap N)).subtype) fun x => congrArg Subtype.val x.2) fun a b h => Subtype.ext (Subtype.ext (by have := congrArg Subtype.val h; exact this)))` and prove the remaining obligations.
-/
theorem length_le_map_add {X Y : Type} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y)
    (N : Submodule R X) : Module.length R N ≤ Module.length R (N.map f) + Module.length R (LinearMap.ker f) := by
  rw [Module.length_eq_add_of_exact (LinearMap.ker (f.submoduleMap N)).subtype (f.submoduleMap N)
    (Submodule.subtype_injective _) (LinearMap.submoduleMap_surjective f N) (LinearMap.exact_subtype_ker_map _), add_comm]
  refine add_le_add le_rfl (Module.length_le_of_injective
    (LinearMap.codRestrict _ (N.subtype.comp (LinearMap.ker (f.submoduleMap N)).subtype)
      fun x => congrArg Subtype.val x.2) fun a b h => Subtype.ext (Subtype.ext (by have := congrArg Subtype.val h; exact this)))

/- English proof (translation)
Use `len_le_of_layers ⊤ _ (fun n => EqHom N (levU l ⊤ n) ρ) (fun m n h => (restrMem F Ω N _ _ _ R M ρ).2.1) (eqExt F Ω l N ⊤ R M ρ hN (by simp) hρ).1 Bd fun n₀ => ?_` and prove the remaining obligations. Take `⟨n, h, hn⟩` from `hB (max n₀ 2)`. Use `⟨n, (le_max_left _ _).trans h, ?_⟩` and prove the remaining obligations. Rewrite using `[← (pullEq F Ω (Fn F Ω l n) _ (galOf_Fn n).ge N R M ρ hN (galOf_Fn n).le (Or.inl ((fnCyc F Ω l n).2.2 ((le_max_right _ _).trans h)))).1]`. Conclude with `(length_map_le _ _).trans hn`.
-/
theorem eqHom_le_of_cl (N : ℕ) (hN : N ≠ 0) (ρ : Representation R (G F Ω) M) (hρ : ∀ m, IsLocallyConstant fun g => ρ g m)
    (Bd : ℕ∞) (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length R (ClEq (Fn F Ω l n) N ρ) ≤ Bd) :
    Module.length R (EqHom N (Uinf F Ω l) ρ) ≤ Bd := by
  refine len_le_of_layers ⊤ _ (fun n => EqHom N (levU l ⊤ n) ρ) (fun m n h => (restrMem F Ω N _ _ _ R M ρ).2.1)
    (eqExt F Ω l N ⊤ R M ρ hN (by simp) hρ).1 Bd fun n₀ => ?_
  obtain ⟨n, h, hn⟩ := hB (max n₀ 2)
  refine ⟨n, (le_max_left _ _).trans h, ?_⟩
  rw [← (pullEq F Ω (Fn F Ω l n) _ (galOf_Fn n).ge N R M ρ hN (galOf_Fn n).le
    (Or.inl ((fnCyc F Ω l n).2.2 ((le_max_right _ _).trans h)))).1]
  exact (length_map_le _ _).trans hn

/- English proof (translation)
Use `len_le_of_layers ⊤ _ (fun n => EqEig N (levU l ⊤ n) ρ σ s) (fun m n h => (restrMem F Ω N _ _ _ R M ρ).2.2 σ s) ((eqExt F Ω l N ⊤ R M ρ hN (by simp) hρ).2 τ σ hσ s fun _ _ => trivial) Bd fun n₀ => ?_` and prove the remaining obligations. Take `⟨n, h, hn⟩` from `hB (max n₀ 2)`. Use `⟨n, (le_max_left _ _).trans h, ?_⟩` and prove the remaining obligations. Take `⟨τ', h'⟩` from `(fnCyc F Ω l n).2.1 τ σ hσ`. Rewrite using `[← (pullEq F Ω (Fn F Ω l n) _ (galOf_Fn n).ge N R M ρ hN (galOf_Fn n).le (Or.inl ((fnCyc F Ω l n).2.2 ((le_max_right _ _).trans h)))).2 τ' σ s h']`.

Conclude with `(length_map_le _ _).trans hn`.
-/
theorem eqEig_le_of_cl (N : ℕ) (hN : N ≠ 0) (ρ : Representation R (G F Ω) M) (hρ : ∀ m, IsLocallyConstant fun g => ρ g m)
    {τ : F ≃+* F} {σ : Ω ≃+* Ω} (hσ : IsLift τ σ) (s : R)
    (Bd : ℕ∞) (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length R (ClEig (Fn F Ω l n) N ρ σ s) ≤ Bd) :
    Module.length R (EqEig N (Uinf F Ω l) ρ σ s) ≤ Bd := by
  refine len_le_of_layers ⊤ _ (fun n => EqEig N (levU l ⊤ n) ρ σ s) (fun m n h => (restrMem F Ω N _ _ _ R M ρ).2.2 σ s)
    ((eqExt F Ω l N ⊤ R M ρ hN (by simp) hρ).2 τ σ hσ s fun _ _ => trivial) Bd fun n₀ => ?_
  obtain ⟨n, h, hn⟩ := hB (max n₀ 2)
  refine ⟨n, (le_max_left _ _).trans h, ?_⟩
  obtain ⟨τ', h'⟩ := (fnCyc F Ω l n).2.1 τ σ hσ
  rw [← (pullEq F Ω (Fn F Ω l n) _ (galOf_Fn n).ge N R M ρ hN (galOf_Fn n).le
    (Or.inl ((fnCyc F Ω l n).2.2 ((le_max_right _ _).trans h)))).2 τ' σ s h']
  exact (length_map_le _ _).trans hn

/- English proof (translation)
Rewrite `hw` using `[KStar.TotallyRealRoots.mem_princ]`. Take `⟨c, hc⟩` from `hw`. Establish `h1 : ((w : ℤ_[l]) - 1) • x = 0`. Rewrite using `[hc, mul_comm ((l : ℤ_[l]) ^ k) c, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hx, smul_zero]`. Rewrite `h1` using `[sub_smul, one_smul, sub_eq_zero]`.

Conclude with `h1`.
-/
private theorem princ_smul_eq_self_of_pow_smul_eq_zero {k : ℕ} {x : QZ l} (hx : l ^ k • x = 0) {w : ℤ_[l]ˣ}
    (hw : w ∈ KStar.TotallyRealRoots.princ l k) : (w : ℤ_[l]) • x = x := by
  rw [KStar.TotallyRealRoots.mem_princ] at hw
  obtain ⟨c, hc⟩ := hw
  have h1 : ((w : ℤ_[l]) - 1) • x = 0 := by
    rw [hc, mul_comm ((l : ℤ_[l]) ^ k) c, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hx, smul_zero]
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `g0`. Take `⟨k, hk⟩` from `(qzBasic l).2.1 m`. Establish `hc : Continuous fun g => cycZ F Ω l g * (cycZ F Ω l g0)⁻¹` using `(continuous_cycZ F Ω l).mul continuous_const`. Establish `hmem : ∀ᶠ g in nhds g0, cycZ F Ω l g * (cycZ F Ω l g0)⁻¹ ∈ KStar.TotallyRealRoots.princ l k`.

Apply `hc.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Apply `(KStar.TotallyRealRoots.isOpen_princ k).mem_nhds` to reduce the goal to its premises. Simplify using `only [mul_inv_cancel]`. Conclude with `(KStar.TotallyRealRoots.princ l k).one_mem`. Use `filter_upwards [hmem] with g hg`.

Use `show ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m = ((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m`. Establish `hw : (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) ∈ KStar.TotallyRealRoots.princ l k` using `zpow_mem hg _`. Establish `hx : l ^ k • (((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m) = 0`. Rewrite using `[smul_comm, hk, smul_zero]`. Establish `key : cycZ F Ω l g ^ (-e) = (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) * cycZ F Ω l g0 ^ (-e)`.

Rewrite using `[← mul_zpow, inv_mul_cancel_right]`. Rewrite using `[key, Units.val_mul, mul_smul, princ_smul_eq_self_of_pow_smul_eq_zero hx hw]`.
-/
theorem locConst_qzG (e : ℤ) (m : QZ l) : IsLocallyConstant fun g => qzG F Ω l e g m := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  obtain ⟨k, hk⟩ := (qzBasic l).2.1 m
  have hc : Continuous fun g => cycZ F Ω l g * (cycZ F Ω l g0)⁻¹ :=
    (continuous_cycZ F Ω l).mul continuous_const
  have hmem : ∀ᶠ g in nhds g0, cycZ F Ω l g * (cycZ F Ω l g0)⁻¹ ∈ KStar.TotallyRealRoots.princ l k := by
    apply hc.continuousAt.preimage_mem_nhds
    apply (KStar.TotallyRealRoots.isOpen_princ k).mem_nhds
    simp only [mul_inv_cancel]
    exact (KStar.TotallyRealRoots.princ l k).one_mem
  filter_upwards [hmem] with g hg
  show ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m = ((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m
  have hw : (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) ∈ KStar.TotallyRealRoots.princ l k := zpow_mem hg _
  have hx : l ^ k • (((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m) = 0 := by
    rw [smul_comm, hk, smul_zero]
  have key : cycZ F Ω l g ^ (-e) =
      (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) * cycZ F Ω l g0 ^ (-e) := by
    rw [← mul_zpow, inv_mul_cancel_right]
  rw [key, Units.val_mul, mul_smul, princ_smul_eq_self_of_pow_smul_eq_zero hx hw]

/- English proof (translation)
The claim follows from `(length_le_map_add (resInf D e) N).trans (add_le_add (Module.length_le_of_injective _ (Submodule.inclusion_injective h)) (resInfKer F Ω l D e he))`.
-/
theorem len_le_of_resInf (D : LData F Ω l) {e : ℤ} (he : e ≠ 0) (N : Submodule ℤ_[l] (H1 (qzTw D e)))
    (W : Submodule ℤ_[l] (Uinf F Ω l → QZ l)) (h : N.map (resInf D e) ≤ W) :
    Module.length ℤ_[l] N ≤ Module.length ℤ_[l] W + errTwo l :=
  (length_le_map_add (resInf D e) N).trans
    (add_le_add (Module.length_le_of_injective _ (Submodule.inclusion_injective h)) (resInfKer F Ω l D e he))

/- English proof (translation)
The claim follows from `len_le_of_resInf D he _ _ (resInfMem F Ω l D e)`.
-/
theorem shaLen_le_eqHom (D : LData F Ω l) {e : ℤ} (he : e ≠ 0) :
    shaLen D e ≤ Module.length ℤ_[l] (EqHom l (Uinf F Ω l) (qzG F Ω l e)) + errTwo l :=
  len_le_of_resInf D he _ _ (resInfMem F Ω l D e)

/- English proof (translation)
The claim follows from `(shaLen_le_eqHom D he).trans (add_le_add (eqHom_le_of_cl l (Fact.out : l.Prime).ne_zero _ (locConst_qzG e) Bd hB) le_rfl)`.
-/
theorem shaLen_le_of_cl (D : LData F Ω l) {e : ℤ} (he : e ≠ 0) (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length ℤ_[l] (ClEq (Fn F Ω l n) l (qzG F Ω l e)) ≤ Bd) :
    shaLen D e ≤ Bd + errTwo l :=
  (shaLen_le_eqHom D he).trans
    (add_le_add (eqHom_le_of_cl l (Fact.out : l.Prime).ne_zero _ (locConst_qzG e) Bd hB) le_rfl)

variable [IsCMField F]

/- English proof (translation)
The claim follows from `len_le_of_resInf D (by exact_mod_cast he) _ _ (resInfSign F Ω l D e σ hσ).1`.
-/
theorem plusLen_le_eqEig (D : LData F Ω l) {e : ℕ} (he : e ≠ 0) {σ : Ω ≃+* Ω} (hσ : IsConjOm σ) :
    plusLen D e ≤ Module.length ℤ_[l] (EqEig l (Uinf F Ω l) (qzG F Ω l e) σ 1) + errTwo l :=
  len_le_of_resInf D (by exact_mod_cast he) _ _ (resInfSign F Ω l D e σ hσ).1

/- English proof (translation)
The claim follows from `len_le_of_resInf D (by exact_mod_cast he) _ _ (resInfSign F Ω l D e σ hσ).2`.
-/
theorem minusLen_le_eqEig (D : LData F Ω l) {e : ℕ} (he : e ≠ 0) {σ : Ω ≃+* Ω} (hσ : IsConjOm σ) :
    minusLen D e ≤ Module.length ℤ_[l] (EqEig l (Uinf F Ω l) (qzG F Ω l e) σ (-1)) + errTwo l :=
  len_le_of_resInf D (by exact_mod_cast he) _ _ (resInfSign F Ω l D e σ hσ).2

/- English proof (translation)
The claim follows from `(plusLen_le_eqEig D he hσ).trans (add_le_add (eqEig_le_of_cl l (Fact.out : l.Prime).ne_zero _ (locConst_qzG _) hσ.isLift 1 Bd hB) le_rfl)`.
-/
theorem plusLen_le_of_cl (D : LData F Ω l) {e : ℕ} (he : e ≠ 0) {σ : Ω ≃+* Ω} (hσ : IsConjOm σ) (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length ℤ_[l] (ClEig (Fn F Ω l n) l (qzG F Ω l e) σ 1) ≤ Bd) :
    plusLen D e ≤ Bd + errTwo l :=
  (plusLen_le_eqEig D he hσ).trans
    (add_le_add (eqEig_le_of_cl l (Fact.out : l.Prime).ne_zero _ (locConst_qzG _) hσ.isLift 1 Bd hB) le_rfl)

/- English proof (translation)
The claim follows from `(minusLen_le_eqEig D he hσ).trans (add_le_add (eqEig_le_of_cl l (Fact.out : l.Prime).ne_zero _ (locConst_qzG _) hσ.isLift (-1) Bd hB) le_rfl)`.
-/
theorem minusLen_le_of_cl (D : LData F Ω l) {e : ℕ} (he : e ≠ 0) {σ : Ω ≃+* Ω} (hσ : IsConjOm σ) (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length ℤ_[l] (ClEig (Fn F Ω l n) l (qzG F Ω l e) σ (-1)) ≤ Bd) :
    minusLen D e ≤ Bd + errTwo l :=
  (minusLen_le_eqEig D he hσ).trans
    (add_le_add (eqEig_le_of_cl l (Fact.out : l.Prime).ne_zero _ (locConst_qzG _) hσ.isLift (-1) Bd hB) le_rfl)

end Lim

end UpperTheory.V.Kum

end
