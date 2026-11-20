import Mathlib
import Formalism.PeriodIntegrals.ScalRelRepFree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

namespace PI.UnitaryGroupMassFormula.ScalRelRepFree

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Unfold `orth`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
theorem mem_orth' {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  unfold orth
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
Conclude with `mem_orth'.mpr fun x hx => mem_orth'.mp hv x (h hx)`.
-/
theorem orth_anti' {U U' : Submodule E S.V} (h : U ≤ U') {v : S.V} (hv : v ∈ orth S U') :
    v ∈ orth S U := by
  exact mem_orth'.mpr fun x hx => mem_orth'.mp hv x (h hx)

/- English proof (translation)
Conclude with `hφ a b`.
-/
theorem isom_apply {φ : S.V ≃ₗ[E] S.V} (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (a b : S.V) :
    S.hT (φ a) (φ b) = S.hT a b := by
  exact hφ a b

/- English proof (translation)
Rewrite using `[← isom_apply hφ (φ.symm a) (φ.symm b), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem isom_symm {φ : S.V ≃ₗ[E] S.V} (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (a b : S.V) :
    S.hT (φ.symm a) (φ.symm b) = S.hT a b := by
  rw [← isom_apply hφ (φ.symm a) (φ.symm b), LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/- English proof (translation)
Use `show ∀ x y, S.hT ((φ.trans ψ) x) ((φ.trans ψ) y) = S.hT x y`. Introduce `x y`. Simplify using `only [LinearEquiv.trans_apply]`. Rewrite using `[isom_apply hψ, isom_apply hφ]`.
-/
theorem isom_trans {φ ψ : S.V ≃ₗ[E] S.V} (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom S.hT) :
    φ.trans ψ ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  show ∀ x y, S.hT ((φ.trans ψ) x) ((φ.trans ψ) y) = S.hT x y
  intro x y
  simp only [LinearEquiv.trans_apply]
  rw [isom_apply hψ, isom_apply hφ]

/- English proof (translation)
Simplify using `only [mem_orth']`. Prove the components needed by the constructor for the conclusion. Introduce `hw x hx`. Rewrite using `[← isom_apply hφ, LinearEquiv.apply_symm_apply]`. Conclude with `hw _ ((hU _).mpr (by simpa using hx))`.

Introduce `hw x hx`. Rewrite using `[← isom_symm hφ]`. Conclude with `hw _ ((hU x).mp hx)`.
-/
theorem orth_transport {φ : S.V ≃ₗ[E] S.V} (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {U U' : Submodule E S.V}
    (hU : ∀ v, v ∈ U' ↔ φ.symm v ∈ U) (w : S.V) : w ∈ orth S U' ↔ φ.symm w ∈ orth S U := by
  simp only [mem_orth']
  constructor
  · intro hw x hx
    rw [← isom_apply hφ, LinearEquiv.apply_symm_apply]
    exact hw _ ((hU _).mpr (by simpa using hx))
  · intro hw x hx
    rw [← isom_symm hφ]
    exact hw _ ((hU x).mp hx)

section Lat

variable {Λ : Submodule (𝓞 E) S.V}

/- English proof (translation)
Take `⟨-, h2⟩` from `h`. Rewrite using `[← h2]`. Unfold `Formalism.HermitianLatticesTheory.gmap`. Conclude with `Submodule.mem_map_of_mem hv`.
-/
theorem aut_mem {φ : S.V ≃ₗ[E] S.V} (h : IsAutLam S Λ φ) {v : S.V} (hv : v ∈ Λ) : φ v ∈ Λ := by
  obtain ⟨-, h2⟩ := h
  rw [← h2]
  unfold Formalism.HermitianLatticesTheory.gmap
  exact Submodule.mem_map_of_mem hv

/- English proof (translation)
Take `⟨-, h2⟩` from `h`. Rewrite `hv` using `[← h2]`. Unfold `Formalism.HermitianLatticesTheory.gmap at hv`. Take `⟨u, hu, huv⟩` from `Submodule.mem_map.mp hv`. Establish `hsu : φ.symm v = u`.

Rewrite using `[← huv]`. Simplify using the standard rewrite rules. Rewrite using `[hsu]`. Conclude with `hu`.
-/
theorem aut_symm_mem {φ : S.V ≃ₗ[E] S.V} (h : IsAutLam S Λ φ) {v : S.V} (hv : v ∈ Λ) : φ.symm v ∈ Λ := by
  obtain ⟨-, h2⟩ := h
  rw [← h2] at hv
  unfold Formalism.HermitianLatticesTheory.gmap at hv
  obtain ⟨u, hu, huv⟩ := Submodule.mem_map.mp hv
  have hsu : φ.symm v = u := by
    rw [← huv]
    simp
  rw [hsu]
  exact hu

/- English proof (translation)
Use `⟨isom_trans hφ.1 hψ.1, ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Unfold `Formalism.HermitianLatticesTheory.gmap`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `aut_mem hψ (aut_mem hφ hu)`. Introduce `hv`. Use `⟨φ.symm (ψ.symm v), aut_symm_mem hφ (aut_symm_mem hψ hv), ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem aut_trans {φ ψ : S.V ≃ₗ[E] S.V} (hφ : IsAutLam S Λ φ) (hψ : IsAutLam S Λ ψ) :
    IsAutLam S Λ (φ.trans ψ) := by
  refine ⟨isom_trans hφ.1 hψ.1, ?_⟩
  ext v
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact aut_mem hψ (aut_mem hφ hu)
  · intro hv
    refine ⟨φ.symm (ψ.symm v), aut_symm_mem hφ (aut_symm_mem hψ hv), ?_⟩
    simp

/- English proof (translation)
Unfold `XLam`. Conclude with `Iff.rfl`.
-/
theorem mem_XLam {T₀ : E} {G : LFlag S r T₀} {v : S.V} : v ∈ XLam Λ G ↔ v ∈ Λ ∧ v ∈ Xsp G := by
  unfold XLam
  exact Iff.rfl

/- English proof (translation)
Unfold `Lrep`. Conclude with `Iff.rfl`.
-/
theorem mem_Lrep {T₀ : E} {G : LFlag S r T₀} {v : S.V} : v ∈ Lrep Λ G ↔ v ∈ Λ ∧ v ∈ orth S (Xsp G) := by
  unfold Lrep
  exact Iff.rfl

/- English proof (translation)
Use `Submodule.smul_induction_on hv (fun a ha m hm => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul_of_tower]`. Conclude with `Submodule.smul_mem_smul ha (hφ m hm)`. Rewrite using `[map_add]`. Conclude with `add_mem hx hy`.
-/
theorem gL_map (φ : S.V →ₗ[E] S.V) (hφ : ∀ v ∈ Λ, φ v ∈ Λ) (g : ℕ) {v : S.V}
    (hv : v ∈ Ideal.span {(g : 𝓞 E)} • Λ) : φ v ∈ Ideal.span {(g : 𝓞 E)} • Λ := by
  refine Submodule.smul_induction_on hv (fun a ha m hm => ?_) (fun x y hx hy => ?_)
  · rw [LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem_smul ha (hφ m hm)
  · rw [map_add]
    exact add_mem hx hy

/- English proof (translation)
Take `⟨y, hy, c, hc, rfl⟩` from `Submodule.mem_sup.mp hv`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hy`. Rewrite using `[map_add, map_add]`. Conclude with `add_mem (add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left (hA a ha))) (Submodule.mem_sup_left (Submodule.mem_sup_right (hB b hb)))) (Submodule.mem_sup_right (hC c hc))`.
-/
theorem map_mem_sup_three (φ : S.V →ₗ[E] S.V) {A B C A' B' C' : Submodule (𝓞 E) S.V}
    (hA : ∀ v ∈ A, φ v ∈ A') (hB : ∀ v ∈ B, φ v ∈ B') (hC : ∀ v ∈ C, φ v ∈ C') {v : S.V}
    (hv : v ∈ A ⊔ B ⊔ C) : φ v ∈ A' ⊔ B' ⊔ C' := by
  obtain ⟨y, hy, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, map_add]
  exact add_mem (add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left (hA a ha)))
    (Submodule.mem_sup_left (Submodule.mem_sup_right (hB b hb))))
    (Submodule.mem_sup_right (hC c hc))

end Lat

/- English proof (translation)
Unfold `Xflag Xsp Formalism.MainNotions.S.FlagG.Xa Formalism.MainNotions.S.FlagG.X`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, -, rfl⟩`. Conclude with `⟨i, rfl⟩`. Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨i, lt_of_lt_of_le i.isLt hj, rfl⟩`.
-/
theorem Xa_ge {T₀ : E} (G : LFlag S r T₀) {j : ℕ} (hj : r ≤ j) : Xflag G j = Xsp G := by
  unfold Xflag Xsp Formalism.MainNotions.S.FlagG.Xa Formalism.MainNotions.S.FlagG.X
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, lt_of_lt_of_le i.isLt hj, rfl⟩

/- English proof (translation)
Rewrite using `[mem_orth']`. Introduce `x hx`. Unfold `Xsp Formalism.MainNotions.S.FlagG.X at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨a, rfl⟩` from `hy`. Conclude with `G.fl.z_orth a`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`. Consider the case `smul c x _ hx => simp [hx]`.
-/
theorem z_orth {T₀ : E} (G : LFlag S r T₀) : G.fl.z ∈ orth S (Xsp G) := by
  rw [mem_orth']
  intro x hx
  unfold Xsp Formalism.MainNotions.S.FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact G.fl.z_orth a
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/- English proof (translation)
Establish `hXp : ∀ {T₂ : E} (G : LFlag S r T₂), Xplus G = Xsp G ⊔ E ∙ G.fl.z`. Introduce `T₂ G`. Unfold `Xplus Xsp`. Use `first`. Consider the case `rfl`.

Consider the case `exact le_antisymm (sInf_le ⟨le_sup_left, le_sup_right⟩) (le_sInf fun x hx => sup_le hx.1 hx.2)`. Rewrite `hv`, the goal using `[hXp]`. Take `⟨x, hx, w, hw, rfl⟩` from `Submodule.mem_sup.mp hv`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hw`. Rewrite using `[map_add, map_smul]`.

Establish `hB : φ A.fl.z ∈ Xsp B ⊔ E ∙ B.fl.z`. Rewrite using `[← sub_add_cancel (φ A.fl.z) B.fl.z]`. Conclude with `add_mem (Submodule.mem_sup_left hz) (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))`. Conclude with `add_mem (Submodule.mem_sup_left (hX x hx)) (Submodule.smul_mem _ c hB)`.
-/
theorem xplus_map {T₀ T₁ : E} {A : LFlag S r T₀} {B : LFlag S r T₁} (φ : S.V →ₗ[E] S.V)
    (hX : ∀ v ∈ Xsp A, φ v ∈ Xsp B) (hz : φ A.fl.z - B.fl.z ∈ Xsp B) {v : S.V} (hv : v ∈ Xplus A) :
    φ v ∈ Xplus B := by
  have hXp : ∀ {T₂ : E} (G : LFlag S r T₂), Xplus G = Xsp G ⊔ E ∙ G.fl.z := by
    intro T₂ G
    unfold Xplus Xsp
    first
    | rfl
    | exact le_antisymm (sInf_le ⟨le_sup_left, le_sup_right⟩)
        (le_sInf fun x hx => sup_le hx.1 hx.2)
  rw [hXp] at hv ⊢
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_add, map_smul]
  have hB : φ A.fl.z ∈ Xsp B ⊔ E ∙ B.fl.z := by
    rw [← sub_add_cancel (φ A.fl.z) B.fl.z]
    exact add_mem (Submodule.mem_sup_left hz)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  exact add_mem (Submodule.mem_sup_left (hX x hx)) (Submodule.smul_mem _ c hB)

section NL

variable {Λ : Submodule (𝓞 E) S.V} {T₀ : E} {G : LFlag S r T₀} {n : S.V ≃ₗ[E] S.V}

/- English proof (translation)
Unfold `NLam at hn`. Take `⟨-, h1, -⟩` from `hn`. Establish `h2` using `h1 r v (by rw [Xa_ge G (by omega : r ≤ r + 1)]; exact hv)`. Rewrite `h2` using `[Xa_ge G le_rfl]`. Then use the resulting hypothesis.
-/
theorem nl_X (hn : n ∈ NLam Λ G) {v : S.V} (hv : v ∈ Xsp G) : n v - v ∈ Xsp G := by
  unfold NLam at hn
  obtain ⟨-, h1, -⟩ := hn
  have h2 := h1 r v (by rw [Xa_ge G (by omega : r ≤ r + 1)]; exact hv)
  rwa [Xa_ge G le_rfl] at h2

/- English proof (translation)
Establish `h` using `add_mem (nl_X hn hv) hv`. Simplify using `using h`.
-/
theorem nl_X_mem (hn : n ∈ NLam Λ G) {v : S.V} (hv : v ∈ Xsp G) : n v ∈ Xsp G := by
  have h := add_mem (nl_X hn hv) hv
  simpa using h

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `nl_X_mem hn hu`. Introduce `v hv haveI : FiniteDimensional E (Xsp G) := by`. Unfold `Xsp Formalism.MainNotions.S.FlagG.X`.

Conclude with `FiniteDimensional.span_of_finite E (Set.finite_range _)`. Set `f : Xsp G →ₗ[E] Xsp G` to `(n : S.V →ₗ[E] S.V).restrict (fun u hu => nl_X_mem hn hu)`. Establish `hinj : Function.Injective f`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `h` using `congrArg Subtype.val hab`. Simplify `h` using `[f]`. Take `⟨u, hu⟩` from `(LinearMap.injective_iff_surjective.mp hinj) ⟨v, hv⟩`. Conclude with `⟨u, u.2, congrArg Subtype.val hu⟩`.
-/
theorem nl_map_X (hn : n ∈ NLam Λ G) : (Xsp G).map (n : S.V →ₗ[E] S.V) = Xsp G := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact nl_X_mem hn hu
  · intro v hv
    haveI : FiniteDimensional E (Xsp G) := by
      unfold Xsp Formalism.MainNotions.S.FlagG.X
      exact FiniteDimensional.span_of_finite E (Set.finite_range _)
    let f : Xsp G →ₗ[E] Xsp G := (n : S.V →ₗ[E] S.V).restrict (fun u hu => nl_X_mem hn hu)
    have hinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have h := congrArg Subtype.val hab
      simpa [f] using h
    obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨v, hv⟩
    exact ⟨u, u.2, congrArg Subtype.val hu⟩

/- English proof (translation)
Rewrite `hv` using `[← nl_map_X hn]`. Take `⟨u, hu, rfl⟩` from `hv`. Simplify using `using hu`.
-/
theorem nl_symm_X (hn : n ∈ NLam Λ G) {v : S.V} (hv : v ∈ Xsp G) : n.symm v ∈ Xsp G := by
  rw [← nl_map_X hn] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  simpa using hu

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify using `using nl_X_mem hn h`. Conclude with `nl_symm_X hn`.
-/
theorem nl_symm_X_iff (hn : n ∈ NLam Λ G) {v : S.V} : n.symm v ∈ Xsp G ↔ v ∈ Xsp G := by
  constructor
  · intro h
    simpa using nl_X_mem hn h
  · exact nl_symm_X hn

/- English proof (translation)
Unfold `NLam at hn`. Conclude with `hn.2.2 v hv`.
-/
theorem nl_orth (hn : n ∈ NLam Λ G) {v : S.V} (hv : v ∈ orth S (Xsp G)) : n v - v ∈ Xsp G := by
  unfold NLam at hn
  exact hn.2.2 v hv

/- English proof (translation)
Establish `hiso : n ∈ Formalism.HermitianLatticesTheory.isom S.hT`. Unfold `NLam at hn`. Conclude with `hn.1.1`. Establish `hu : n.symm v ∈ orth S (Xsp G)`. Rewrite `hv`, the goal using `[mem_orth']`.

Introduce `x hx`. Rewrite using `[← isom_apply hiso, LinearEquiv.apply_symm_apply]`. Conclude with `hv _ (nl_X_mem hn hx)`. Establish `h` using `nl_orth hn hu`. Rewrite `h` using `[LinearEquiv.apply_symm_apply]`.

Establish `h2` using `neg_mem h`. Rewrite `h2` using `[neg_sub]`. Then use the resulting hypothesis.
-/
theorem nl_symm_sub (hn : n ∈ NLam Λ G) {v : S.V} (hv : v ∈ orth S (Xsp G)) : n.symm v - v ∈ Xsp G := by
  have hiso : n ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
    unfold NLam at hn
    exact hn.1.1
  have hu : n.symm v ∈ orth S (Xsp G) := by
    rw [mem_orth'] at hv ⊢
    intro x hx
    rw [← isom_apply hiso, LinearEquiv.apply_symm_apply]
    exact hv _ (nl_X_mem hn hx)
  have h := nl_orth hn hu
  rw [LinearEquiv.apply_symm_apply] at h
  have h2 := neg_mem h
  rwa [neg_sub] at h2

/- English proof (translation)
Establish `hA : IsAutLam S Λ n`. Unfold `NLam at hn`. Conclude with `hn.1`. Rewrite `hv`, the goal using `[mem_XLam]`. Conclude with `⟨aut_mem hA hv.1, nl_X_mem hn hv.2⟩`.
-/
theorem nl_XLam (hn : n ∈ NLam Λ G) {v : S.V} (hv : v ∈ XLam Λ G) : n v ∈ XLam Λ G := by
  have hA : IsAutLam S Λ n := by
    unfold NLam at hn
    exact hn.1
  rw [mem_XLam] at hv ⊢
  exact ⟨aut_mem hA hv.1, nl_X_mem hn hv.2⟩

/- English proof (translation)
Establish `hA : IsAutLam S Λ n`. Unfold `NLam at hn`. Conclude with `hn.1`. Rewrite `hv`, the goal using `[mem_XLam]`. Conclude with `⟨aut_symm_mem hA hv.1, nl_symm_X hn hv.2⟩`.
-/
theorem nl_symm_XLam (hn : n ∈ NLam Λ G) {v : S.V} (hv : v ∈ XLam Λ G) : n.symm v ∈ XLam Λ G := by
  have hA : IsAutLam S Λ n := by
    unfold NLam at hn
    exact hn.1
  rw [mem_XLam] at hv ⊢
  exact ⟨aut_symm_mem hA hv.1, nl_symm_X hn hv.2⟩

/- English proof (translation)
Establish `hA : IsAutLam S Λ n`. Unfold `NLam at hn`. Conclude with `hn.1`. Rewrite using `[mem_XLam]`. Conclude with `⟨sub_mem (aut_mem hA hl) hl, nl_orth hn ho⟩`.
-/
theorem nl_sub_XLam (hn : n ∈ NLam Λ G) {v : S.V} (hl : v ∈ Λ) (ho : v ∈ orth S (Xsp G)) :
    n v - v ∈ XLam Λ G := by
  have hA : IsAutLam S Λ n := by
    unfold NLam at hn
    exact hn.1
  rw [mem_XLam]
  exact ⟨sub_mem (aut_mem hA hl) hl, nl_orth hn ho⟩

/- English proof (translation)
Establish `hA : IsAutLam S Λ n`. Unfold `NLam at hn`. Conclude with `hn.1`. Rewrite using `[mem_XLam]`. Conclude with `⟨sub_mem (aut_symm_mem hA hl) hl, nl_symm_sub hn ho⟩`.
-/
theorem nl_symm_sub_XLam (hn : n ∈ NLam Λ G) {v : S.V} (hl : v ∈ Λ) (ho : v ∈ orth S (Xsp G)) :
    n.symm v - v ∈ XLam Λ G := by
  have hA : IsAutLam S Λ n := by
    unfold NLam at hn
    exact hn.1
  rw [mem_XLam]
  exact ⟨sub_mem (aut_symm_mem hA hl) hl, nl_symm_sub hn ho⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Conclude with `xplus_map (n.symm : S.V →ₗ[E] S.V) (fun u hu => nl_symm_X hn hu) (nl_symm_sub hn (z_orth G)) hv`. Introduce `hv`. Establish `h` using `xplus_map (n : S.V →ₗ[E] S.V) (fun u hu => nl_X_mem hn hu) (nl_orth hn (z_orth G)) hv`.

Simplify using `using h`.
-/
theorem nl_Xplus_iff (hn : n ∈ NLam Λ G) {v : S.V} : v ∈ Xplus G ↔ n.symm v ∈ Xplus G := by
  constructor
  · intro hv
    exact xplus_map (n.symm : S.V →ₗ[E] S.V) (fun u hu => nl_symm_X hn hu)
      (nl_symm_sub hn (z_orth G)) hv
  · intro hv
    have h := xplus_map (n : S.V →ₗ[E] S.V) (fun u hu => nl_X_mem hn hu)
      (nl_orth hn (z_orth G)) hv
    simpa using h

end NL

section UU

variable {Λ : Submodule (𝓞 E) S.V} {T₀ T₁ : E} {F : LFlag S r T₀} {F' : LFlag S r T₁}

/- English proof (translation)
Unfold `UU`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left hv))`.
-/
theorem uu_A {v : S.V} (hv : v ∈ XLam Λ F) : v ∈ UU Λ F F' := by
  unfold UU
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left hv))

/- English proof (translation)
Unfold `UU`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))`.
-/
theorem uu_B : F.zt ∈ UU Λ F F' := by
  unfold UU
  exact Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))

/- English proof (translation)
Unfold `UU`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right hv)`.
-/
theorem uu_C {v : S.V} (hv : v ∈ XLam Λ F') : v ∈ UU Λ F F' := by
  unfold UU
  exact Submodule.mem_sup_left (Submodule.mem_sup_right hv)

/- English proof (translation)
Unfold `UU`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`.
-/
theorem uu_D : F'.zt ∈ UU Λ F F' := by
  unfold UU
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

/- English proof (translation)
Unfold `UUE spanE`. Conclude with `Submodule.subset_span hv`.
-/
theorem uue_of {v : S.V} (hv : v ∈ UU Λ F F') : v ∈ UUE Λ F F' := by
  unfold UUE spanE
  exact Submodule.subset_span hv

/- English proof (translation)
Establish `key : ∀ u ∈ UU Λ F F', φ u ∈ UUE Λ G G'`. Introduce `u hu`. Unfold `UU at hu`. Take `⟨y1, hy1, d, hd, rfl⟩` from `Submodule.mem_sup.mp hu`. Take `⟨y2, hy2, c, hc, rfl⟩` from `Submodule.mem_sup.mp hy1`.

Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hy2`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.mp hb`. Take `⟨t', rfl⟩` from `Submodule.mem_span_singleton.mp hd`. Simplify using `only [map_add, LinearMap.map_smul_of_tower]`. Conclude with `add_mem (add_mem (add_mem (hA a ha) (Submodule.smul_of_tower_mem _ t hB)) (hC c hc)) (Submodule.smul_of_tower_mem _ t' hD)`.

Unfold `UUE spanE at hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem u hu => exact key u hu`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`.

Rewrite using `[map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem uue_map {T₂ T₃ : E} {G : LFlag S r T₂} {G' : LFlag S r T₃} (φ : S.V →ₗ[E] S.V)
    (hA : ∀ v ∈ XLam Λ F, φ v ∈ UUE Λ G G') (hB : φ F.zt ∈ UUE Λ G G')
    (hC : ∀ v ∈ XLam Λ F', φ v ∈ UUE Λ G G') (hD : φ F'.zt ∈ UUE Λ G G') {v : S.V}
    (hv : v ∈ UUE Λ F F') : φ v ∈ UUE Λ G G' := by
  have key : ∀ u ∈ UU Λ F F', φ u ∈ UUE Λ G G' := by
    intro u hu
    unfold UU at hu
    obtain ⟨y1, hy1, d, hd, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨y2, hy2, c, hc, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy2
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
    obtain ⟨t', rfl⟩ := Submodule.mem_span_singleton.mp hd
    simp only [map_add, LinearMap.map_smul_of_tower]
    exact add_mem (add_mem (add_mem (hA a ha) (Submodule.smul_of_tower_mem _ t hB)) (hC c hc))
      (Submodule.smul_of_tower_mem _ t' hD)
  unfold UUE spanE at hv
  induction hv using Submodule.span_induction with
  | mem u hu => exact key u hu
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

end UU

end PI.UnitaryGroupMassFormula.ScalRelRepFree
