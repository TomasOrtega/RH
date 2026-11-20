import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Simplify using `[frame, FlagG.fvec]`.
-/
theorem frame_castSucc_td {T : E} (F : LFlag S r T) (i : Fin r) : frame F i.castSucc = F.fl.e i := by
  simp [frame, FlagG.fvec]

/- English proof (translation)
Simplify using `[frame, FlagG.fvec]`.
-/
theorem frame_last_td {T : E} (F : LFlag S r T) : frame F (Fin.last r) = F.fl.z := by
  simp [frame, FlagG.fvec]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`. Introduce `h`. Conclude with `⟨g.symm x, h, by simp⟩`.
-/
theorem mem_gmap_iff {Λ : Submodule (𝓞 E) S.V} (g : S.V ≃ₗ[E] S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.gmap g Λ ↔ g.symm x ∈ Λ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g.symm x, h, by simp⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x`. Use `(mem_gmap_iff (Λ := Λ) g (g x))` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `using this`.

Introduce `h`. Use extensionality with `x`. Rewrite using `[mem_gmap_iff]`. Use `h (g.symm x)` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem gmap_eq_iff {Λ : Submodule (𝓞 E) S.V} (g : S.V ≃ₗ[E] S.V) :
    Formalism.HermitianLatticesTheory.gmap g Λ = Λ ↔ ∀ x, g x ∈ Λ ↔ x ∈ Λ := by
  constructor
  · intro h x
    have := (mem_gmap_iff (Λ := Λ) g (g x))
    rw [h] at this
    simpa using this
  · intro h
    ext x
    rw [mem_gmap_iff]
    have := h (g.symm x)
    simpa using this.symm

/- English proof (translation)
Unfold `IsAutLam`. Rewrite using `[gmap_eq_iff]`. Both sides reduce to the same expression.
-/
theorem isAutLam_iff (Λ : Submodule (𝓞 E) S.V) (g : S.V ≃ₗ[E] S.V) :
    IsAutLam S Λ g ↔ (∀ x y, S.hT (g x) (g y) = S.hT x y) ∧ ∀ x, g x ∈ Λ ↔ x ∈ Λ := by
  unfold IsAutLam
  rw [gmap_eq_iff]
  rfl

/- English proof (translation)
Rewrite `*` using `[isAutLam_iff]`. Use `⟨fun x y => ?_, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearEquiv.mul_apply]`. Rewrite using `[hg.1, hh.1]`. Simplify using `only [LinearEquiv.mul_apply]`.

Rewrite using `[hg.2, hh.2]`.
-/
theorem isAutLam_mul {Λ : Submodule (𝓞 E) S.V} {g h : S.V ≃ₗ[E] S.V} (hg : IsAutLam S Λ g)
    (hh : IsAutLam S Λ h) : IsAutLam S Λ (g * h) := by
  rw [isAutLam_iff] at *
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · simp only [LinearEquiv.mul_apply]
    rw [hg.1, hh.1]
  · simp only [LinearEquiv.mul_apply]
    rw [hg.2, hh.2]

/- English proof (translation)
Rewrite `*` using `[isAutLam_iff]`. Use `⟨fun x y => ?_, fun x => ?_⟩` and prove the remaining obligations. Use `hg.1 (g⁻¹ x) (g⁻¹ y)` as an intermediate fact. Simplify using `using this.symm`. Use `hg.2 (g⁻¹ x)` as an intermediate fact.

Simplify using `using this.symm`.
-/
theorem isAutLam_inv {Λ : Submodule (𝓞 E) S.V} {g : S.V ≃ₗ[E] S.V} (hg : IsAutLam S Λ g) :
    IsAutLam S Λ g⁻¹ := by
  rw [isAutLam_iff] at *
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have := hg.1 (g⁻¹ x) (g⁻¹ y)
    simpa using this.symm
  · have := hg.2 (g⁻¹ x)
    simpa using this.symm

/- English proof (translation)
Apply `Submodule.span_mono` to reduce the goal to its premises. Apply `Set.image_mono` to reduce the goal to its premises. Introduce `i hi`. Conclude with `lt_of_lt_of_le hi h`.
-/
theorem xflag_mono_td {T : E} (F : LFlag S r T) {j k : ℕ} (h : j ≤ k) : Xflag F j ≤ Xflag F k := by
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  exact lt_of_lt_of_le hi h

/- English proof (translation)
Simplify using `[Xflag, FlagG.Xa]`.
-/
theorem xflag_zero_td {T : E} (F : LFlag S r T) : Xflag F 0 = ⊥ := by
  simp [Xflag, FlagG.Xa]

/- English proof (translation)
Simplify using `only [Xflag, FlagG.Xa, Xsp, FlagG.X]`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem xflag_r {T : E} (F : LFlag S r T) : Xflag F r = Xsp F := by
  simp only [Xflag, FlagG.Xa, Xsp, FlagG.X]
  congr 1
  ext x
  simp

/- English proof (translation)
Introduce `x hx`. Consider the cases of `j with`. Consider the case `zero`. Rewrite `hx`, the goal using `[xflag_zero_td]`. Rewrite `hx`, the goal using `[Submodule.mem_bot]`.

Simplify using `[hx]`. Consider the case `succ k`. Establish `h1` using `hn.2.1 k x hx`. Establish `h2 : n x = x + (n x - x)` using `by abel`. Rewrite using `[h2]`.

Conclude with `Submodule.add_mem _ hx (xflag_mono_td F (Nat.le_succ k) h1)`.
-/
theorem nlam_mapsTo {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) (j : ℕ) : ∀ x ∈ Xflag F j, n x ∈ Xflag F j := by
  intro x hx
  cases j with
  | zero =>
    rw [xflag_zero_td] at hx ⊢
    rw [Submodule.mem_bot] at hx ⊢
    simp [hx]
  | succ k =>
    have h1 := hn.2.1 k x hx
    have h2 : n x = x + (n x - x) := by abel
    rw [h2]
    exact Submodule.add_mem _ hx (xflag_mono_td F (Nat.le_succ k) h1)

/- English proof (translation)
Apply `Submodule.eq_of_le_of_finrank_eq` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `nlam_mapsTo hn j x hx`. Conclude with `LinearEquiv.finrank_map_eq n _`.
-/
theorem nlam_map_eq {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) (j : ℕ) : (Xflag F j).map (n : S.V →ₗ[E] S.V) = Xflag F j := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, hx, rfl⟩
    exact nlam_mapsTo hn j x hx
  · exact LinearEquiv.finrank_map_eq n _

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf]`.
-/
theorem mem_orth_iff_td {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ y ∈ U, S.hT y v = 0 := by
  simp [orth, Submodule.mem_iInf]

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[mem_orth_iff_td]`. Introduce `y hy`. Establish `hy' : y ∈ (Xsp F).map (n : S.V →ₗ[E] S.V)`. Rewrite using `[← xflag_r, nlam_map_eq hn r]`.

Rewrite using `[xflag_r]` and apply the resulting hypothesis. Take `⟨y', hy'X, rfl⟩` from `hy'`. Establish `hiso` using `((isAutLam_iff Λ n).1 hn.1).1`. Simplify using `only [LinearEquiv.coe_coe]`. Rewrite using `[hiso]`.

Conclude with `hx y' hy'X`.
-/
theorem nlam_orth_mapsTo {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) : ∀ x ∈ orth S (Xsp F), n x ∈ orth S (Xsp F) := by
  intro x hx
  rw [mem_orth_iff_td] at hx ⊢
  intro y hy
  have hy' : y ∈ (Xsp F).map (n : S.V →ₗ[E] S.V) := by
    rw [← xflag_r, nlam_map_eq hn r]
    rwa [xflag_r]
  obtain ⟨y', hy'X, rfl⟩ := hy'
  have hiso := ((isAutLam_iff Λ n).1 hn.1).1
  simp only [LinearEquiv.coe_coe]
  rw [hiso]
  exact hx y' hy'X

/- English proof (translation)
Apply `Submodule.eq_of_le_of_finrank_eq` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `nlam_orth_mapsTo hn x hx`. Conclude with `LinearEquiv.finrank_map_eq n _`.
-/
theorem nlam_orth_map_eq {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) : (orth S (Xsp F)).map (n : S.V →ₗ[E] S.V) = orth S (Xsp F) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, hx, rfl⟩
    exact nlam_orth_mapsTo hn x hx
  · exact LinearEquiv.finrank_map_eq n _

/- English proof (translation)
Use `⟨isAutLam_mul hn.1 hp.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `j x hx`. Establish `e : (n * p) x - x = (n (p x) - p x) + (p x - x)`. Simplify using `only [LinearEquiv.mul_apply]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (hn.2.1 j _ (nlam_mapsTo hp (j + 1) x hx)) (hp.2.1 j x hx)`. Introduce `x hx`. Establish `e : (n * p) x - x = (n (p x) - p x) + (p x - x)`. Simplify using `only [LinearEquiv.mul_apply]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (hn.2.2 _ (nlam_orth_mapsTo hp x hx)) (hp.2.2 x hx)`.
-/
theorem nlamPf_mul {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n p : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) (hp : p ∈ NLam Λ F) : n * p ∈ NLam Λ F := by
  refine ⟨isAutLam_mul hn.1 hp.1, ?_, ?_⟩
  · intro j x hx
    have e : (n * p) x - x = (n (p x) - p x) + (p x - x) := by
      simp only [LinearEquiv.mul_apply]; abel
    rw [e]
    exact Submodule.add_mem _ (hn.2.1 j _ (nlam_mapsTo hp (j + 1) x hx)) (hp.2.1 j x hx)
  · intro x hx
    have e : (n * p) x - x = (n (p x) - p x) + (p x - x) := by
      simp only [LinearEquiv.mul_apply]; abel
    rw [e]
    exact Submodule.add_mem _ (hn.2.2 _ (nlam_orth_mapsTo hp x hx)) (hp.2.2 x hx)

/- English proof (translation)
Use `⟨isAutLam_inv hn.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `j x hx`. Rewrite `hx` using `[← nlam_map_eq hn (j + 1)]`. Take `⟨y, hy, rfl⟩` from `hx`. Establish `e : n⁻¹ ((n : S.V →ₗ[E] S.V) y) - (n : S.V →ₗ[E] S.V) y = -(n y - y)`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `Submodule.neg_mem _ (hn.2.1 j y hy)`. Introduce `x hx`. Rewrite `hx` using `[← nlam_orth_map_eq hn]`.

Take `⟨y, hy, rfl⟩` from `hx`. Establish `e : n⁻¹ ((n : S.V →ₗ[E] S.V) y) - (n : S.V →ₗ[E] S.V) y = -(n y - y)`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `Submodule.neg_mem _ (hn.2.2 y hy)`.
-/
theorem nlamPf_inv {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) : n⁻¹ ∈ NLam Λ F := by
  refine ⟨isAutLam_inv hn.1, ?_, ?_⟩
  · intro j x hx
    rw [← nlam_map_eq hn (j + 1)] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have e : n⁻¹ ((n : S.V →ₗ[E] S.V) y) - (n : S.V →ₗ[E] S.V) y = -(n y - y) := by
      simp
    rw [e]
    exact Submodule.neg_mem _ (hn.2.1 j y hy)
  · intro x hx
    rw [← nlam_orth_map_eq hn] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have e : n⁻¹ ((n : S.V →ₗ[E] S.V) y) - (n : S.V →ₗ[E] S.V) y = -(n y - y) := by
      simp
    rw [e]
    exact Submodule.neg_mem _ (hn.2.2 y hy)

/- English proof (translation)
Establish `he : ∀ i, F₂.fl.e i = γ (F₁.fl.e i)`. Introduce `i`. Use `hF i.castSucc` as an intermediate fact. Rewrite `this` using `[frame_castSucc_td, frame_castSucc_td]`. Then use the resulting hypothesis. Establish `hm : Xflag F₂ j = (Xflag F₁ j).map (γ : S.V →ₗ[E] S.V)`.

Simplify using `only [Xflag, FlagG.Xa, Submodule.map_span]`. Use `congr 1`. Use extensionality with `y`. Simplify using `[he]`. Rewrite using `[hm]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`. Introduce `h`. Conclude with `⟨γ.symm x, h, by simp⟩`.
-/
theorem mem_xflag_of_frame {T₁ T₂ : E} {F₁ : LFlag S r T₁} {F₂ : LFlag S r T₂} {γ : S.V ≃ₗ[E] S.V}
    (hF : ∀ a, frame F₂ a = γ (frame F₁ a)) (j : ℕ) (x : S.V) :
    x ∈ Xflag F₂ j ↔ γ.symm x ∈ Xflag F₁ j := by
  have he : ∀ i, F₂.fl.e i = γ (F₁.fl.e i) := by
    intro i
    have := hF i.castSucc
    rwa [frame_castSucc_td, frame_castSucc_td] at this
  have hm : Xflag F₂ j = (Xflag F₁ j).map (γ : S.V →ₗ[E] S.V) := by
    simp only [Xflag, FlagG.Xa, Submodule.map_span]
    congr 1
    ext y
    simp [he]
  rw [hm]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨γ.symm x, h, by simp⟩

/- English proof (translation)
Rewrite using `[← xflag_r, ← xflag_r]`. Conclude with `mem_xflag_of_frame hF r x`.
-/
theorem mem_xsp_of_frame {T₁ T₂ : E} {F₁ : LFlag S r T₁} {F₂ : LFlag S r T₂} {γ : S.V ≃ₗ[E] S.V}
    (hF : ∀ a, frame F₂ a = γ (frame F₁ a)) (x : S.V) :
    x ∈ Xsp F₂ ↔ γ.symm x ∈ Xsp F₁ := by
  rw [← xflag_r, ← xflag_r]
  exact mem_xflag_of_frame hF r x

/- English proof (translation)
Rewrite using `[mem_orth_iff_td, mem_orth_iff_td]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Use `h (γ y) (by rw [mem_xsp_of_frame hF]; simpa using hy)` as an intermediate fact. Rewrite using `[← hγ y (γ.symm x)]`.

Simplify using `using this`. Introduce `h y hy`. Use `h (γ.symm y) ((mem_xsp_of_frame hF y).1 hy)` as an intermediate fact. Rewrite `this` using `[← hγ (γ.symm y) (γ.symm x)]`. Simplify using `using this`.
-/
theorem mem_orth_of_frame {T₁ T₂ : E} {F₁ : LFlag S r T₁} {F₂ : LFlag S r T₂} {γ : S.V ≃ₗ[E] S.V}
    (hF : ∀ a, frame F₂ a = γ (frame F₁ a)) (hγ : ∀ x y, S.hT (γ x) (γ y) = S.hT x y) (x : S.V) :
    x ∈ orth S (Xsp F₂) ↔ γ.symm x ∈ orth S (Xsp F₁) := by
  rw [mem_orth_iff_td, mem_orth_iff_td]
  constructor
  · intro h y hy
    have := h (γ y) (by rw [mem_xsp_of_frame hF]; simpa using hy)
    rw [← hγ y (γ.symm x)]
    simpa using this
  · intro h y hy
    have := h (γ.symm y) ((mem_xsp_of_frame hF y).1 hy)
    rw [← hγ (γ.symm y) (γ.symm x)] at this
    simpa using this

/- English proof (translation)
Establish `hiso` using `((isAutLam_iff Λ γ).1 hγ).1`. Use `⟨isAutLam_mul (isAutLam_mul hγ hp.1) (isAutLam_inv hγ), ?_, ?_⟩` and prove the remaining obligations. Introduce `j x hx`. Rewrite `hx`, the goal using `[mem_xflag_of_frame hF]`. Use `hp.2.1 j _ hx` as an intermediate fact.

Establish `e : γ.symm ((γ * p * γ⁻¹) x - x) = p (γ.symm x) - γ.symm x`. Simplify using `only [LinearEquiv.mul_apply, map_sub]`. Simplify using `[LinearEquiv.coe_inv]`. Rewrite using `[e]`. Conclude with `this`.

Introduce `x hx`. Rewrite `hx` using `[mem_orth_of_frame hF hiso]`. Rewrite using `[mem_xsp_of_frame hF]`. Use `hp.2.2 _ hx` as an intermediate fact. Establish `e : γ.symm ((γ * p * γ⁻¹) x - x) = p (γ.symm x) - γ.symm x`.

Simplify using `only [LinearEquiv.mul_apply, map_sub]`. Simplify using `[LinearEquiv.coe_inv]`. Rewrite using `[e]`. Conclude with `this`.
-/
theorem nlam_conj {Λ : Submodule (𝓞 E) S.V} {T₁ T₂ : E} {F₁ : LFlag S r T₁} {F₂ : LFlag S r T₂} {γ p : S.V ≃ₗ[E] S.V}
    (hγ : IsAutLam S Λ γ) (hF : ∀ a, frame F₂ a = γ (frame F₁ a)) (hp : p ∈ NLam Λ F₁) :
    γ * p * γ⁻¹ ∈ NLam Λ F₂ := by
  have hiso := ((isAutLam_iff Λ γ).1 hγ).1
  refine ⟨isAutLam_mul (isAutLam_mul hγ hp.1) (isAutLam_inv hγ), ?_, ?_⟩
  · intro j x hx
    rw [mem_xflag_of_frame hF] at hx ⊢
    have := hp.2.1 j _ hx
    have e : γ.symm ((γ * p * γ⁻¹) x - x) = p (γ.symm x) - γ.symm x := by
      simp only [LinearEquiv.mul_apply, map_sub]
      simp [LinearEquiv.coe_inv]
    rw [e]
    exact this
  · intro x hx
    rw [mem_orth_of_frame hF hiso] at hx
    rw [mem_xsp_of_frame hF]
    have := hp.2.2 _ hx
    have e : γ.symm ((γ * p * γ⁻¹) x - x) = p (γ.symm x) - γ.symm x := by
      simp only [LinearEquiv.mul_apply, map_sub]
      simp [LinearEquiv.coe_inv]
    rw [e]
    exact this

variable (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T)

/- English proof (translation)
Take `⟨n, hn, m, hm, hfr, hzt⟩` from `h`. Establish `hγ : IsAutLam S Λ (n * m)` using `isAutLam_mul hn.1 hm.1`. Establish `hF : ∀ a, frame F₂ a = (n * m) (frame F₁ a)` using `fun a => by simpa using hfr a`. Establish `hm'` using `nlam_conj hγ hF (nlamPf_inv hm)`. Use `⟨n⁻¹, nlamPf_inv hn, n * m * m⁻¹ * (n * m)⁻¹, hm', fun a => ?_, ?_⟩` and prove the remaining obligations.

Establish `key : n⁻¹ * (n * m * m⁻¹ * (n * m)⁻¹) * (n * m) = 1` using `by group`. Use `congrArg (fun q : S.V ≃ₗ[E] S.V => q (frame F₁ a)) key` as an intermediate fact. Simplify using `only [LinearEquiv.mul_apply] at this`. Rewrite using `[hfr a]`. Simplify using `using this.symm`.

Establish `key : n⁻¹ * (n * m * m⁻¹ * (n * m)⁻¹) * (n * m) = 1` using `by group`. Use `congrArg (fun q : S.V ≃ₗ[E] S.V => q F₁.zt) key` as an intermediate fact. Simplify using `only [LinearEquiv.mul_apply] at this`. Rewrite using `[hzt]`. Simplify using `using this.symm`.
-/
theorem dcrel_symm {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) : DCRel Λ F F₂ F₁ := by
  obtain ⟨n, hn, m, hm, hfr, hzt⟩ := h
  have hγ : IsAutLam S Λ (n * m) := isAutLam_mul hn.1 hm.1
  have hF : ∀ a, frame F₂ a = (n * m) (frame F₁ a) := fun a => by simpa using hfr a
  have hm' := nlam_conj hγ hF (nlamPf_inv hm)
  refine ⟨n⁻¹, nlamPf_inv hn, n * m * m⁻¹ * (n * m)⁻¹, hm', fun a => ?_, ?_⟩
  · have key : n⁻¹ * (n * m * m⁻¹ * (n * m)⁻¹) * (n * m) = 1 := by group
    have := congrArg (fun q : S.V ≃ₗ[E] S.V => q (frame F₁ a)) key
    simp only [LinearEquiv.mul_apply] at this
    rw [hfr a]
    simpa using this.symm
  · have key : n⁻¹ * (n * m * m⁻¹ * (n * m)⁻¹) * (n * m) = 1 := by group
    have := congrArg (fun q : S.V ≃ₗ[E] S.V => q F₁.zt) key
    simp only [LinearEquiv.mul_apply] at this
    rw [hzt]
    simpa using this.symm

/- English proof (translation)
Take `⟨n, hn, m, hm, hfr, hzt⟩` from `h`. Take `⟨n', hn', m', hm', hfr', hzt'⟩` from `h'`. Establish `hγ : IsAutLam S Λ (n * m)⁻¹` using `isAutLam_inv (isAutLam_mul hn.1 hm.1)`. Establish `hF : ∀ a, frame F₁ a = (n * m)⁻¹ (frame F₂ a)` using `fun a => by`. Rewrite using `[hfr a]`.

Simplify using `[LinearEquiv.coe_inv]`. Establish `hm''` using `nlam_conj hγ hF hm'`. Use `⟨n' * n, nlamPf_mul hn' hn, m * ((n * m)⁻¹ * m' * (n * m)⁻¹⁻¹), nlamPf_mul hm hm'', fun a => ?_, ?_⟩` and prove the remaining obligations. Establish `key : (n' * n) * (m * ((n * m)⁻¹ * m' * (n * m)⁻¹⁻¹)) = n' * m' * (n * m)` using `by group`. Use `congrArg (fun q : S.V ≃ₗ[E] S.V => q (frame F₁ a)) key` as an intermediate fact.

Rewrite using `[hfr' a, hfr a]`. Simplify using `only [LinearEquiv.mul_apply] at this ⊢`. Conclude with `this.symm`. Establish `key : (n' * n) * (m * ((n * m)⁻¹ * m' * (n * m)⁻¹⁻¹)) = n' * m' * (n * m)` using `by group`. Use `congrArg (fun q : S.V ≃ₗ[E] S.V => q F₁.zt) key` as an intermediate fact.

Rewrite using `[hzt', hzt]`. Simplify using `only [LinearEquiv.mul_apply] at this ⊢`. Conclude with `this.symm`.
-/
theorem dcrel_trans {F₁ F₂ F₃ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) (h' : DCRel Λ F F₂ F₃) :
    DCRel Λ F F₁ F₃ := by
  obtain ⟨n, hn, m, hm, hfr, hzt⟩ := h
  obtain ⟨n', hn', m', hm', hfr', hzt'⟩ := h'
  have hγ : IsAutLam S Λ (n * m)⁻¹ := isAutLam_inv (isAutLam_mul hn.1 hm.1)
  have hF : ∀ a, frame F₁ a = (n * m)⁻¹ (frame F₂ a) := fun a => by
    rw [hfr a]; simp [LinearEquiv.coe_inv]
  have hm'' := nlam_conj hγ hF hm'
  refine ⟨n' * n, nlamPf_mul hn' hn, m * ((n * m)⁻¹ * m' * (n * m)⁻¹⁻¹), nlamPf_mul hm hm'', fun a => ?_, ?_⟩
  · have key : (n' * n) * (m * ((n * m)⁻¹ * m' * (n * m)⁻¹⁻¹)) = n' * m' * (n * m) := by group
    have := congrArg (fun q : S.V ≃ₗ[E] S.V => q (frame F₁ a)) key
    rw [hfr' a, hfr a]
    simp only [LinearEquiv.mul_apply] at this ⊢
    exact this.symm
  · have key : (n' * n) * (m * ((n * m)⁻¹ * m' * (n * m)⁻¹⁻¹)) = n' * m' * (n * m) := by group
    have := congrArg (fun q : S.V ≃ₗ[E] S.V => q F₁.zt) key
    rw [hzt', hzt]
    simp only [LinearEquiv.mul_apply] at this ⊢
    exact this.symm

variable (P : LFlag S r T' → Prop)

/- English proof (translation)
Introduce `x y`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hq` using `Quot.eqvGen_exact h`. Use `clear h`.

Proceed by induction on `hq with`. Consider the case `rel a b hab => exact hab`. Consider the case `refl a => exact dcrel_refl Λ F a.1`. Consider the case `symm a b _ ih => exact dcrel_symm Λ F ih`. Consider the case `trans a b c _ _ ih1 ih2 => exact dcrel_trans Λ F ih1 ih2`.

Introduce `h`. Conclude with `Quot.sound h`.
-/
theorem double_coset_equivalence : EqIff Λ F P := by
  intro x y
  constructor
  · intro h
    have hq := Quot.eqvGen_exact h
    clear h
    induction hq with
    | rel a b hab => exact hab
    | refl a => exact dcrel_refl Λ F a.1
    | symm a b _ ih => exact dcrel_symm Λ F ih
    | trans a b c _ _ ih1 ih2 => exact dcrel_trans Λ F ih1 ih2
  · intro h
    exact Quot.sound h

section Zhat

variable {Λ : Submodule (𝓞 E) S.V}

/- English proof (translation)
Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Rewrite using `[frame_last_td]`. Establish `hz : F.fl.z ∈ orth S (Xsp F)`. Rewrite using `[mem_orth_iff_td]`.

Introduce `y hy`. Use `Submodule.span_induction ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `F.fl.z_orth i`. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy`. Simplify using `[map_add, hx, hy]`. Introduce `c x _ hx`. Simplify using `[hx]`. Use `hn.2.2 _ hz` as an intermediate fact.

Use `Submodule.span_mono ?_ this` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨i.castSucc, Fin.castSucc_lt_last i, frame_castSucc_td F i⟩`. Consider the case `cast i`. Rewrite using `[frame_castSucc_td]`.

Establish `hx : F.fl.e i ∈ Xflag F (i.1 + 1)` using `Submodule.subset_span ⟨i, by simp, rfl⟩`. Use `hn.2.1 i.1 _ hx` as an intermediate fact. Use `Submodule.span_mono ?_ this` and prove the remaining obligations. Introduce and unpack `_ ⟨i', hi', rfl⟩`. Conclude with `⟨i'.castSucc, Fin.castSucc_lt_castSucc_iff.mpr hi', frame_castSucc_td F i'⟩`.
-/
theorem frame_sub_mem_span {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F)
    (a : Fin (r + 1)) : n (frame F a) - frame F a ∈ Submodule.span E (frame F '' {c | c < a}) := by
  induction a using Fin.lastCases with
  | last =>
    rw [frame_last_td]
    have hz : F.fl.z ∈ orth S (Xsp F) := by
      rw [mem_orth_iff_td]
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, rfl⟩
        exact F.fl.z_orth i
      · simp
      · intro x y _ _ hx hy
        simp [map_add, hx, hy]
      · intro c x _ hx
        simp [hx]
    have := hn.2.2 _ hz
    refine Submodule.span_mono ?_ this
    rintro _ ⟨i, rfl⟩
    exact ⟨i.castSucc, Fin.castSucc_lt_last i, frame_castSucc_td F i⟩
  | cast i =>
    rw [frame_castSucc_td]
    have hx : F.fl.e i ∈ Xflag F (i.1 + 1) := Submodule.subset_span ⟨i, by simp, rfl⟩
    have := hn.2.1 i.1 _ hx
    refine Submodule.span_mono ?_ this
    rintro _ ⟨i', hi', rfl⟩
    exact ⟨i'.castSucc, Fin.castSucc_lt_castSucc_iff.mpr hi', frame_castSucc_td F i'⟩

/- English proof (translation)
Establish `h` using `fun a => (Finsupp.mem_span_image_iff_linearCombination E).1 (frame_sub_mem_span hn a)`. Use `choose l hl hsum using h`. Establish `hz : ∀ a c, ¬ c < a → l a c = 0` using `fun a c hc => (Finsupp.mem_supported' _ _).1 (hl a) c hc`. Use `⟨fun a c => (if a = c then 1 else 0) + l a c, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a c hac`.

Simplify using `[ne_of_lt hac, hz a c (not_lt.2 (le_of_lt hac))]`. Introduce `a`. Simplify using `[hz a a (lt_irrefl a)]`. Introduce `a`. Establish `e` using `hsum a`.

Rewrite `e` using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[e]`. Normalize the expressions using the abelian group laws.
-/
theorem nlam_coef {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    ∃ α : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a c, a < c → α a c = 0) ∧ (∀ a, α a a = 1) ∧
      ∀ a, n (frame F a) = ∑ c, α a c • frame F c := by
  have h := fun a => (Finsupp.mem_span_image_iff_linearCombination E).1 (frame_sub_mem_span hn a)
  choose l hl hsum using h
  have hz : ∀ a c, ¬ c < a → l a c = 0 := fun a c hc => (Finsupp.mem_supported' _ _).1 (hl a) c hc
  refine ⟨fun a c => (if a = c then 1 else 0) + l a c, ?_, ?_, ?_⟩
  · intro a c hac
    simp [ne_of_lt hac, hz a c (not_lt.2 (le_of_lt hac))]
  · intro a
    simp [hz a a (lt_irrefl a)]
  · intro a
    have e := hsum a
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [e]
    abel

/- English proof (translation)
Take `⟨n, hn, m, hm, hfr, -⟩` from `h`. Take `⟨α, hα0, hα1, hα⟩` from `nlam_coef (nlamPf_inv hn)`. Take `⟨β, hβ0, hβ1, hβ⟩` from `nlam_coef hm`. Use `⟨α.map star, β.transpose, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a c h`.

Simplify using `[hα0 a c h]`. Introduce `a`. Simplify using `[hα1]`. Introduce `d b h`. Simplify using `[Matrix.transpose_apply, hβ0 b d h]`.

Introduce `b`. Simplify using `[hβ1]`. Use extensionality with `a b`. Establish `hiso` using `((isAutLam_iff Λ n).1 hn.1).1`. Establish `e1 : ZhatL F F₂ a b = S.hT (n⁻¹ (frame F a)) (m (frame F₁ b))`.

Express the relevant statement in the definitionally equal form `S.hT (frame F a) (frame F₂ b) = _`. Rewrite using `[hfr b, ← hiso (n⁻¹ (frame F a)) (m (frame F₁ b))]`. Simplify using the standard rewrite rules. Rewrite using `[e1, hα a, hβ b]`. Simplify using `only [Matrix.mul_apply, ZhatL, Zhat, brS, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]`.

Simplify using `only [Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]`. Use `Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zhat_rel {T T' : E} (F : LFlag S r T) {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) :
    ∃ A B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a c, a < c → A a c = 0) ∧ (∀ a, A a a = 1) ∧
      (∀ d b, b < d → B d b = 0) ∧ (∀ b, B b b = 1) ∧ ZhatL F F₂ = A * ZhatL F F₁ * B := by
  obtain ⟨n, hn, m, hm, hfr, -⟩ := h
  obtain ⟨α, hα0, hα1, hα⟩ := nlam_coef (nlamPf_inv hn)
  obtain ⟨β, hβ0, hβ1, hβ⟩ := nlam_coef hm
  refine ⟨α.map star, β.transpose, ?_, ?_, ?_, ?_, ?_⟩
  · intro a c h
    simp [hα0 a c h]
  · intro a
    simp [hα1]
  · intro d b h
    simp [Matrix.transpose_apply, hβ0 b d h]
  · intro b
    simp [hβ1]
  · ext a b
    have hiso := ((isAutLam_iff Λ n).1 hn.1).1
    have e1 : ZhatL F F₂ a b = S.hT (n⁻¹ (frame F a)) (m (frame F₁ b)) := by
      change S.hT (frame F a) (frame F₂ b) = _
      rw [hfr b, ← hiso (n⁻¹ (frame F a)) (m (frame F₁ b))]
      simp
    rw [e1, hα a, hβ b]
    simp only [Matrix.mul_apply, ZhatL, Zhat, brS, map_sum, map_smulₛₗ, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
    simp only [Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => ?_))
    ring

/- English proof (translation)
Use `(Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ g ?_ (fun _ => rfl)).symm` and prove the remaining obligations. Introduce `d hd`. Apply `hg` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`. Conclude with `hd ⟨⟨d.1, by omega⟩, Fin.ext (by simp)⟩`.
-/
theorem sum_castLE_td {N l : ℕ} (h : l ≤ N) (g : Fin N → E) (hg : ∀ d : Fin N, l ≤ d.1 → g d = 0) :
    ∑ d, g d = ∑ d' : Fin l, g (Fin.castLE h d') := by
  refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ g ?_ (fun _ => rfl)).symm
  intro d hd
  apply hg
  by_contra hlt
  exact hd ⟨⟨d.1, by omega⟩, Fin.ext (by simp)⟩

/- English proof (translation)
Unfold `leadMinorE`. Use `split_ifs with h`. Establish `hsub : (A * Z * B).submatrix (Fin.castLE h) (Fin.castLE h) = A.submatrix (Fin.castLE h) (Fin.castLE h) * Z.submatrix (Fin.castLE h) (Fin.castLE h) * B.submatrix (Fin.castLE h) (Fin.castLE h)`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`.

Rewrite using `[sum_castLE_td h]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Use `congr 1`. Rewrite using `[sum_castLE_td h]`. Introduce `c hc`.

Rewrite using `[hA0 _ _ (by rw [Fin.lt_def]; simp; omega), zero_mul]`. Introduce `d hd`. Rewrite using `[hB0 _ _ (by rw [Fin.lt_def]; simp; omega), mul_zero]`. Rewrite using `[hsub, Matrix.det_mul, Matrix.det_mul]`. Establish `hA : (A.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1`.

Rewrite using `[Matrix.det_of_lowerTriangular]`. Simplify using `[hA1]`. Introduce `i j hij`. Conclude with `hA0 _ _ (by`. Establish `: i < j` using `hij`.

Rewrite `this`, the goal using `[Fin.lt_def]`. Simplify using `using this)`. Establish `hB : (B.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1`. Rewrite using `[Matrix.det_of_upperTriangular]`. Simplify using `[hB1]`.

Introduce `i j hij`. Conclude with `hB0 _ _ (by`. Establish `: j < i` using `hij`. Rewrite `this`, the goal using `[Fin.lt_def]`. Simplify using `using this)`.

Rewrite using `[hA, hB, one_mul, mul_one]`. Both sides reduce to the same expression.
-/
theorem leadMinor_uni {N : ℕ} (A Z B : Matrix (Fin N) (Fin N) E) (hA0 : ∀ a c, a < c → A a c = 0)
    (hA1 : ∀ a, A a a = 1) (hB0 : ∀ d b, b < d → B d b = 0) (hB1 : ∀ b, B b b = 1) (l : ℕ) :
    leadMinorE (A * Z * B) l = leadMinorE Z l := by
  unfold leadMinorE
  split_ifs with h
  · have hsub : (A * Z * B).submatrix (Fin.castLE h) (Fin.castLE h) =
        A.submatrix (Fin.castLE h) (Fin.castLE h) * Z.submatrix (Fin.castLE h) (Fin.castLE h) *
          B.submatrix (Fin.castLE h) (Fin.castLE h) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [sum_castLE_td h]
      · refine Finset.sum_congr rfl (fun d _ => ?_)
        congr 1
        rw [sum_castLE_td h]
        intro c hc
        rw [hA0 _ _ (by rw [Fin.lt_def]; simp; omega), zero_mul]
      · intro d hd
        rw [hB0 _ _ (by rw [Fin.lt_def]; simp; omega), mul_zero]
    rw [hsub, Matrix.det_mul, Matrix.det_mul]
    have hA : (A.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
      rw [Matrix.det_of_lowerTriangular]
      · simp [hA1]
      · intro i j hij
        exact hA0 _ _ (by
          have : i < j := hij
          rw [Fin.lt_def] at this ⊢
          simpa using this)
    have hB : (B.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
      rw [Matrix.det_of_upperTriangular]
      · simp [hB1]
      · intro i j hij
        exact hB0 _ _ (by
          have : j < i := hij
          rw [Fin.lt_def] at this ⊢
          simpa using this)
    rw [hA, hB, one_mul, mul_one]
  · rfl

/- English proof (translation)
Take `⟨A, B, hA0, hA1, hB0, hB1, hZ⟩` from `zhat_rel F h`. Establish `hD : ∀ l, Dl F.fl F₂.fl l = Dl F.fl F₁.fl l`. Introduce `l`. Use `leadMinor_uni A (ZhatL F F₁) B hA0 hA1 hB0 hB1 l` as an intermediate fact. Rewrite `this` using `[← hZ]`.

Conclude with `this`. Simplify using `only [Gval, Gflag, hD]`.
-/
theorem gval_rel {T T' : E} (F : LFlag S r T) {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) :
    Gval F F₂ = Gval F F₁ := by
  obtain ⟨A, B, hA0, hA1, hB0, hB1, hZ⟩ := zhat_rel F h
  have hD : ∀ l, Dl F.fl F₂.fl l = Dl F.fl F₁.fl l := by
    intro l
    have := leadMinor_uni A (ZhatL F F₁) B hA0 hA1 hB0 hB1 l
    rw [← hZ] at this
    exact this
  simp only [Gval, Gflag, hD]

/- English proof (translation)
Introduce `i j`. Prove the components needed by the constructor for the conclusion. Introduce `hij`. Simplify using `only [Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `k _`. Break down `lt_or_ge i k with h | h` into its components or cases. Simplify using `[(hA i k).1 h]`. Simplify using `[(hL k j).1 (lt_of_le_of_lt h hij)]`. Introduce and unpack `rfl`.

Simplify using `only [Matrix.mul_apply]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[(hA i i).2 rfl, (hL i i).2 rfl]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases.

Simplify using `[(hL k i).1 h]`. Simplify using `[(hA i k).1 h]`. Simplify using the standard rewrite rules.
-/
theorem isLoUni_mul {N : ℕ} {A L : Matrix (Fin N) (Fin N) E} (hA : IsLoUni A) (hL : IsLoUni L) :
    IsLoUni (A * L) := by
  intro i j
  constructor
  · intro hij
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge i k with h | h
    · simp [(hA i k).1 h]
    · simp [(hL k j).1 (lt_of_le_of_lt h hij)]
  · rintro rfl
    simp only [Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · simp [(hA i i).2 rfl, (hL i i).2 rfl]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [(hL k i).1 h]
      · simp [(hA i k).1 h]
    · simp

/- English proof (translation)
Introduce `i j`. Prove the components needed by the constructor for the conclusion. Introduce `hij`. Simplify using `only [Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `k _`. Break down `lt_or_ge k i with h | h` into its components or cases. Simplify using `[(hU i k).1 h]`. Simplify using `[(hV k j).1 (lt_of_lt_of_le hij h)]`. Introduce and unpack `rfl`.

Simplify using `only [Matrix.mul_apply]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[(hU i i).2 rfl, (hV i i).2 rfl]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases.

Simplify using `[(hU i k).1 h]`. Simplify using `[(hV k i).1 h]`. Simplify using the standard rewrite rules.
-/
theorem isUpUni_mul {N : ℕ} {U V : Matrix (Fin N) (Fin N) E} (hU : IsUpUni U) (hV : IsUpUni V) :
    IsUpUni (U * V) := by
  intro i j
  constructor
  · intro hij
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge k i with h | h
    · simp [(hU i k).1 h]
    · simp [(hV k j).1 (lt_of_lt_of_le hij h)]
  · rintro rfl
    simp only [Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · simp [(hU i i).2 rfl, (hV i i).2 rfl]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [(hU i k).1 h]
      · simp [(hV k i).1 h]
    · simp

/- English proof (translation)
Establish `hs : ∀ k : ℕ, (-1 : E) ^ k * (-1) ^ k = 1` using `fun k => by`. Rewrite using `[← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules. Use extensionality with `a b`. Simplify using `only [ZhatOM, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Matrix.of_apply]`.

Use `Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ => ?_))` and prove the remaining obligations. Take the linear combination `(-(A a c * Z c d * B d b * (-1) ^ (r - b.val))) * hs (r - d.val)`.
-/
theorem zhatOM_mul (A Z B : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    ZhatOM (A * Z * B) =
      A * ZhatOM Z * Matrix.of (fun d b => (-1 : E) ^ (r - d.val) * B d b * (-1) ^ (r - b.val)) := by
  have hs : ∀ k : ℕ, (-1 : E) ^ k * (-1) ^ k = 1 := fun k => by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  ext a b
  simp only [ZhatOM, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Matrix.of_apply]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ => ?_))
  linear_combination (-(A a c * Z c d * B d b * (-1) ^ (r - b.val))) * hs (r - d.val)

/- English proof (translation)
Take `⟨A, B, hA0, hA1, hB0, hB1, hZ⟩` from `zhat_rel F h`. Take `⟨L, U, hL, hU, hLU⟩` from `hc`. Use `⟨A * L, U * Matrix.of (fun d b => (-1 : E) ^ (r - d.val) * B d b * (-1) ^ (r - b.val)), isLoUni_mul (fun i j => ⟨hA0 i j, fun e => e ▸ hA1 i⟩) hL, isUpUni_mul hU ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Prove the components needed by the constructor for the conclusion.

Introduce `hij`. Simplify using `[Matrix.of_apply, hB0 i j hij]`. Introduce and unpack `rfl`. Rewrite using `[Matrix.of_apply, hB1, mul_one, ← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[hZ, zhatOM_mul, hLU]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem cell_rel {T T' : E} (F : LFlag S r T) {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂)
    (w : Point E (r + 1)) (hc : IsInCell (ZhatOM (ZhatL F F₁)) w) :
    IsInCell (ZhatOM (ZhatL F F₂)) w := by
  obtain ⟨A, B, hA0, hA1, hB0, hB1, hZ⟩ := zhat_rel F h
  obtain ⟨L, U, hL, hU, hLU⟩ := hc
  refine ⟨A * L, U * Matrix.of (fun d b => (-1 : E) ^ (r - d.val) * B d b * (-1) ^ (r - b.val)),
    isLoUni_mul (fun i j => ⟨hA0 i j, fun e => e ▸ hA1 i⟩) hL, isUpUni_mul hU ?_, ?_⟩
  · intro i j
    constructor
    · intro hij
      simp [Matrix.of_apply, hB0 i j hij]
    · rintro rfl
      rw [Matrix.of_apply, hB1, mul_one, ← pow_add, ← two_mul, pow_mul]
      simp
  · rw [hZ, zhatOM_mul, hLU]
    simp only [Matrix.mul_assoc]

end Zhat

section Props

variable (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (P : LFlag S r T' → Prop)

/- English proof (translation)
Introduce `_ _ h` and use `(gval_rel F h).symm`.
-/
theorem g_value_function : GFun Λ F P := fun _ _ h => (gval_rel F h).symm

/- English proof (translation)
Introduce `_ _ h w` and use `⟨cell_rel F h w, cell_rel F (dcrel_symm Λ F h) w⟩`.
-/
theorem cell_function_holds : CellFun Λ F P := fun _ _ h w =>
  ⟨cell_rel F h w, cell_rel F (dcrel_symm Λ F h) w⟩

end Props

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

/- English proof (translation)
Introduce `F0 Λ _` and use `double_coset_equivalence Λ (lf D F0) _`.
-/
theorem term_equivalence_iff (u u' : D.what₂.Word) : TermEqIff D u u' :=
  fun F0 Λ _ => double_coset_equivalence Λ (lf D F0) _

end D7

end Formalism.L2.SG.Pf
