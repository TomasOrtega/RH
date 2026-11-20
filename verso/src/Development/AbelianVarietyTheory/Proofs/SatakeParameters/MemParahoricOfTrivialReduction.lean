import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.CongLevel

section Ext

variable {k : Type} [CommRing k] {n : ℕ} (c : ℕ)

def resX : (Fin (n + c) → k) →ₗ[k] (Fin n → k) := LinearMap.funLeft k k (Fin.castAdd c)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem inX_apply (x : Fin n → k) (l : Fin (n + c)) :
    Loc.inX k n c x l = if h : l.1 < n then x ⟨l.1, h⟩ else 0 := by
  unfold Loc.inX
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem resX_inX (x : Fin n → k) : resX c (Loc.inX k n c x) = x := by
  funext i
  show Loc.inX k n c x (Fin.castAdd c i) = _
  rw [inX_apply, dif_pos (by simp)]
  rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem resX_eN (i : ℕ) : resX c (Loc.eN k (n + c) (n + i)) = 0 := by
  funext l
  show Loc.eN k (n + c) (n + i) (Fin.castAdd c l) = 0
  have := l.2
  unfold Loc.eN
  rw [if_neg]
  simp only [Fin.val_castAdd]
  omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem inX_mem_Ufl (i : ℕ) (x : Fin n → k) : Loc.inX k n c x ∈ Loc.Ufl k n c i := by
  intro l hl
  rw [inX_apply, dif_neg]
  intro h
  exact hl (show l.1 < n + i by omega)

def extL (a : (Fin n → k) →ₗ[k] (Fin n → k)) : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.id + Loc.inX k n c ∘ₗ (a - LinearMap.id) ∘ₗ resX c

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem extL_apply (a : (Fin n → k) →ₗ[k] (Fin n → k)) (v : Fin (n + c) → k) :
    extL c a v = v + Loc.inX k n c (a (resX c v) - resX c v) := rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem extL_extL (a b : (Fin n → k) →ₗ[k] (Fin n → k)) (hab : ∀ x, a (b x) = x) (v : Fin (n + c) → k) :
    extL c a (extL c b v) = v := by
  have h : resX c (extL c b v) = b (resX c v) := by
    rw [extL_apply, map_add, resX_inX]; abel
  rw [extL_apply c a, h, hab, extL_apply, map_sub, map_sub]
  abel

def extE (κ : (Fin n → k) ≃ₗ[k] (Fin n → k)) : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k) :=
  LinearEquiv.ofLinear (extL c κ.toLinearMap) (extL c κ.symm.toLinearMap)
    (LinearMap.ext fun v => extL_extL c _ _ (fun x => κ.apply_symm_apply x) v)
    (LinearMap.ext fun v => extL_extL c _ _ (fun x => κ.symm_apply_apply x) v)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem extE_apply (κ : (Fin n → k) ≃ₗ[k] (Fin n → k)) (v : Fin (n + c) → k) :
    extE c κ v = v + Loc.inX k n c (κ (resX c v) - resX c v) := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem extE_inv (κ : (Fin n → k) ≃ₗ[k] (Fin n → k)) : (extE c κ)⁻¹ = extE c κ⁻¹ :=
  LinearEquiv.ext fun _ => rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem extE_R1cond (κ : (Fin n → k) ≃ₗ[k] (Fin n → k)) : Loc.R1cond k n c (extE c κ) := by
  have h : ∀ i, extE c κ (Loc.eN k (n + c) (n + i)) = Loc.eN k (n + c) (n + i) := by
    intro i
    rw [extE_apply, resX_eN]
    simp
  refine ⟨fun i v hv => ?_, h 0, fun i => ?_⟩
  · rw [extE_apply]
    exact add_mem hv (inX_mem_Ufl c i _)
  · rw [h, sub_self]
    exact zero_mem _

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup (κ : (Fin n → k) ≃ₗ[k] (Fin n → k)) : extE c κ ∈ Loc.R1 k n c :=
  ⟨extE_R1cond c κ, by rw [extE_inv]; exact extE_R1cond c _⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem extE_inX (κ : (Fin n → k) ≃ₗ[k] (Fin n → k)) (x : Fin n → k) :
    extE c κ (Loc.inX k n c x) = Loc.inX k n c (κ x) := by
  rw [extE_apply, resX_inX, map_sub]
  abel

end Ext

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem mem_sclLat (N : ℕ) (e : ℕ → ℤ) (x : Sp E N) :
    x ∈ LocE.sclLat P q N e ↔ ∀ l : Fin N, IntAt P (((q : E) ^ e l.1)⁻¹ * x l) := by
  unfold LocE.sclLat stdAt
  rw [Submodule.mem_comap, mem_localization_standardLattice]
  rfl

omit [StarRing E] in
/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem intAt_nat (m : ℕ) : IntAt P (m : E) := by
  simpa using IntAt.coe P (m : 𝓞 E)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Clear the denominators using the available nonvanishing facts. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem sclLat_le (hq : (q : E) ≠ 0) (N : ℕ) (e : ℕ → ℤ) (p : ℕ → Prop) [DecidablePred p] :
    LocE.sclLat P q N (fun l => e l + if p l then 1 else 0) ≤ LocE.sclLat P q N e := by
  intro x hx
  rw [mem_sclLat] at hx ⊢
  intro l
  have h := hx l
  by_cases hp : p l.1
  · rw [if_pos hp] at h
    have h2 := (intAt_nat P q).mul h
    convert h2 using 1
    rw [zpow_add₀ hq, zpow_one]
    have := zpow_ne_zero (e l.1) hq
    field_simp
  · rw [if_neg hp, add_zero] at h
    exact h

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Clear the denominators using the available nonvanishing facts.
-/
theorem smul_mem_sclLat (hq : (q : E) ≠ 0) (N : ℕ) (e : ℕ → ℤ) (p : ℕ → Prop) [DecidablePred p]
    (x : Sp E N) (hx : (q : E)⁻¹ • x ∈ LocE.sclLat P q N e) :
    x ∈ LocE.sclLat P q N (fun l => e l + if p l then 1 else 0) := by
  rw [mem_sclLat] at hx ⊢
  intro l
  have h := hx l
  rw [Pi.smul_apply, smul_eq_mul] at h
  have := zpow_ne_zero (e l.1) hq
  by_cases hp : p l.1
  · rw [if_pos hp]
    convert h using 1
    rw [zpow_add₀ hq, zpow_one]
    field_simp
  · rw [if_neg hp, add_zero]
    have h2 := (intAt_nat P q).mul h
    convert h2 using 1
    field_simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem bvec_mem (hq : (q : E) ≠ 0) (N : ℕ) (e : ℕ → ℤ) (f : ℕ) :
    ((q : E) ^ e f) • Loc.eN E N f ∈ LocE.sclLat P q N e := by
  rw [mem_sclLat]
  intro l
  rw [Pi.smul_apply, smul_eq_mul]
  unfold Loc.eN
  split_ifs with h
  · rw [h, mul_one, inv_mul_cancel₀ (zpow_ne_zero _ hq)]
    simpa using intAt_nat P 1
  · simpa using intAt_nat P 0

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Supply the required witnesses or components.
-/
theorem mem_flagU {N : ℕ} (L : Submodule (𝓞 E) (Sp E N)) (M : ℕ → Submodule (𝓞 E) (Sp E N)) (e : ℕ → Sp E N)
    (r : ℕ) (st : Set ℕ) (hM : ∀ s, M s ≤ L) (hM' : ∀ s x, (q : E)⁻¹ • x ∈ L → x ∈ M s) (he : ∀ s, e s ∈ L)
    (g : Sp E N ≃ₗ[E] Sp E N) (hg : g ∈ stabL E N L) (hc : ∀ x ∈ L, (q : E)⁻¹ • (g x - x) ∈ L) :
    g ∈ LocE.flagU M e r st := by
  have hs : ∀ s, g ∈ stabL E N (M s) := by
    intro s x
    constructor
    · intro hx
      have h1 := hM' s _ (hc x ((hg x).1 (hM s hx)))
      have := sub_mem hx h1
      rwa [sub_sub_cancel] at this
    · intro hx
      have h1 := hM' s _ (hc x (hM s hx))
      have := add_mem h1 hx
      rwa [sub_add_cancel] at this
  exact ⟨fun s _ => hs s, fun s _ => ⟨hs s, hM' s _ (hc _ (he s))⟩⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem inX_mem_lamY {n : ℕ} (c : ℕ) (ex : ℕ → ℕ) (x : Sp E n) (hx : x ∈ stdAt E n P) :
    Loc.inX E n c x ∈ LocE.lamY P q n c ex := by
  unfold LocE.lamY
  rw [mem_sclLat]
  intro l
  rw [inX_apply]
  split_ifs with h
  · unfold LocE.scE
    rw [if_pos h, zpow_zero, inv_one, one_mul]
    exact (mem_localization_standardLattice P x).1 hx _
  · simpa using intAt_nat P 0

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem resX_mem {n : ℕ} (c : ℕ) (ex : ℕ → ℕ) (v : Sp E (n + c)) (hv : v ∈ LocE.lamY P q n c ex) :
    resX c v ∈ stdAt E n P := by
  unfold LocE.lamY at hv
  rw [mem_sclLat] at hv
  refine (mem_localization_standardLattice P _).2 fun i => ?_
  have h := hv (Fin.castAdd c i)
  unfold LocE.scE at h
  rw [if_pos (by simp), zpow_zero, inv_one, one_mul] at h
  exact h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem extE_maps {n : ℕ} (c : ℕ) (ex : ℕ → ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : κ ∈ GLint E n P)
    (v : Sp E (n + c)) (hv : v ∈ LocE.lamY P q n c ex) : extE c κ v ∈ LocE.lamY P q n c ex := by
  rw [extE_apply]
  have h := resX_mem P q c ex v hv
  exact add_mem hv (inX_mem_lamY P q c ex _ (sub_mem ((hκ _).2 h) h))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem extE_stab {n : ℕ} (c : ℕ) (ex : ℕ → ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : κ ∈ GLint E n P) :
    extE c κ ∈ stabL E (n + c) (LocE.lamY P q n c ex) := by
  intro v
  refine ⟨fun hv => ?_, extE_maps P q c ex κ hκ v⟩
  have h := extE_maps P q c ex κ⁻¹ (inv_mem hκ) _ hv
  rw [← extE_inv] at h
  rwa [show (extE c κ)⁻¹ (extE c κ v) = v from LinearEquiv.symm_apply_apply _ v] at h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem extE_cong {n : ℕ} (c : ℕ) (ex : ℕ → ℕ) (hd : ∀ a : E, IntAt P a → redP P a = 0 → IntAt P (a / (q : E)))
    (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : κ ∈ GLint E n P) (hr : ∀ x ∈ stdAt E n P, redV P (κ x) = redV P x)
    (v : Sp E (n + c)) (hv : v ∈ LocE.lamY P q n c ex) :
    (q : E)⁻¹ • (extE c κ v - v) ∈ LocE.lamY P q n c ex := by
  rw [extE_apply, add_sub_cancel_left, ← map_smul]
  have h := resX_mem P q c ex v hv
  refine inX_mem_lamY P q c ex _ ((mem_localization_standardLattice P _).2 fun i => ?_)
  have h1 := (mem_localization_standardLattice P _).1 (sub_mem ((hκ _).2 h) h) i
  have h2 := (mem_localization_standardLattice P _).1 h i
  have h3 : redP P (κ (resX c v) i) = redP P (resX c v i) := congrFun (hr _ h) i
  have h4 := reduction_add h1 h2
  rw [Pi.sub_apply, sub_add_cancel, h3] at h4
  have h5 := hd _ h1 (by rw [Pi.sub_apply]; exact (add_eq_right.1 h4.symm))
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, ← div_eq_mul_inv]
  exact h5

omit [StarRing E] in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conj_cong {N : ℕ} (L : Submodule (𝓞 E) (Sp E N)) (g h : Sp E N ≃ₗ[E] Sp E N) (hh : h ∈ stabL E N L)
    (hc : ∀ x ∈ L, (q : E)⁻¹ • (g x - x) ∈ L) : ∀ x ∈ L, (q : E)⁻¹ • ((h⁻¹ * g * h) x - x) ∈ L := by
  intro x hx
  refine (hh _).1 ?_
  rw [map_smul, map_sub, show h ((h⁻¹ * g * h) x) = g (h x) from LinearEquiv.apply_symm_apply _ _]
  exact hc _ ((hh x).2 hx)

end Lat

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Replace the relevant objects with their definitions.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem cong_mem_prCat : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs → (∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E))) → ∀ h : AutY X R j, h ∈ stabL X.E _ (lamYat (Pr := Pr) j w) → ∀ κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j), κ ∈ GLint X.E (R.N j) w → (∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) → κ ∈ prCat (Pr := Pr) sharp j w h := by
  intro X Pr R sharp j w hw hd h hh κ hκ hr
  have hq : ((qOf w : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  unfold lamYat at hh
  rw [if_pos hw] at hh
  refine ⟨extE _ κ, ⟨extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ κ, ?_⟩, extE_inX _ κ⟩
  have e : (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) = h⁻¹ * extE (cOf R j) κ * h := by simp
  show (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) ∈ Jat (Pr := Pr) sharp j w
  rw [e]
  have hs := mul_mem (mul_mem (inv_mem hh) (extE_stab w (qOf w) (cOf R j) (fun i => i + 1) κ hκ)) hh
  have hc := conj_cong (qOf w) _ _ h hh (extE_cong w (qOf w) (cOf R j) (fun i => i + 1) hd κ hκ hr)
  unfold Jat
  rw [if_pos hw]
  split_ifs
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _

end GlobalTheory.CongLevel
