import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.PairLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' T₂ : E}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ}

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
theorem mem_orth {U : Submodule E S.V} {x : S.V} : x ∈ orth S U ↔ ∀ u ∈ U, S.hT u x = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Establish `h` using `S.herm.eq (F.fl.e a) F.fl.z`. Rewrite `h` using `[F.fl.z_orth a]`.

Simplify using `using h.symm`. Consider the case `zero => simp`. Consider the case `add y z _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul c y _ h => simp [h]`.
-/
theorem hT_z_X (F : LFlag S r T) {x : S.V} (hx : x ∈ Xsp F) : S.hT F.fl.z x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have h := S.herm.eq (F.fl.e a) F.fl.z
    rw [F.fl.z_orth a] at h
    simpa using h.symm
  | zero => simp
  | add y z _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Submodule.span E (Set.range F.fl.e) = Submodule.span E (F.fl.e '' {i | i.1 < r})`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `⟨a, a.2, rfl⟩`. Introduce and unpack `⟨a, _, rfl⟩`. Conclude with `⟨a, rfl⟩`.
-/
theorem X_eq_Xflag (F : LFlag S r T) : Xsp F = Xflag F r := by
  change Submodule.span E (Set.range F.fl.e) = Submodule.span E (F.fl.e '' {i | i.1 < r})
  congr 1
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, _, rfl⟩
    exact ⟨a, rfl⟩

/- English proof (translation)
Establish `hlo : l ∈ orth S (Xsp F)` using `(Submodule.mem_inf.1 hl).2`. Establish `hy : y = l + (y - l)` using `by abel`. Use `Submodule.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hy]`. Conclude with `Submodule.add_mem_sup hl h`.

Rewrite using `[hy]`. Conclude with `(orth S (Xsp F)).add_mem hlo (FrEqv.X_le_orth h)`.
-/
theorem mem_Lsub_of {F : LFlag S r T} {l y : S.V} (hl : l ∈ Lrep Λ F) (h : y - l ∈ Xsp F) :
    y ∈ Lsub Λ F := by
  have hlo : l ∈ orth S (Xsp F) := (Submodule.mem_inf.1 hl).2
  have hy : y = l + (y - l) := by abel
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [hy]
    exact Submodule.add_mem_sup hl h
  · rw [hy]
    exact (orth S (Xsp F)).add_mem hlo (FrEqv.X_le_orth h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, Submodule.zero_mem _, by simp, 0, Submodule.zero_mem _, by simp, by simp⟩`.
-/
theorem IotaRel_zero (F : LFlag S r T) (F' : LFlag S r T') : IotaRel Λ g F F' 0 :=
  ⟨0, Submodule.zero_mem _, by simp, 0, Submodule.zero_mem _, by simp, by simp⟩

/- English proof (translation)
Take `⟨l, hl, h1, l', hl', h2, h3⟩` from `hx`. Take `⟨m, hm, k1, m', hm', k2, k3⟩` from `hy`. Use `⟨l + m, Submodule.add_mem _ hl hm, ?_, l' + m', Submodule.add_mem _ hl' hm', ?_, ?_⟩` and prove the remaining obligations. Use `(Xsp F).add_mem h1 k1` as an intermediate fact. Rewrite `this` using `[show x - l + (y - m) = x + y - (l + m) by abel]`. Then use the resulting hypothesis.

Use `(Xsp F').add_mem h2 k2` as an intermediate fact. Rewrite `this` using `[show x - l' + (y - m') = x + y - (l' + m') by abel]`. Then use the resulting hypothesis. Use `Submodule.add_mem _ h3 k3` as an intermediate fact. Rewrite `this` using `[show l - l' + (m - m') = l + m - (l' + m') by abel]`. Then use the resulting hypothesis.
-/
theorem IotaRel_add {F : LFlag S r T} {F' : LFlag S r T'} {x y : S.V}
    (hx : IotaRel Λ g F F' x) (hy : IotaRel Λ g F F' y) : IotaRel Λ g F F' (x + y) := by
  obtain ⟨l, hl, h1, l', hl', h2, h3⟩ := hx
  obtain ⟨m, hm, k1, m', hm', k2, k3⟩ := hy
  refine ⟨l + m, Submodule.add_mem _ hl hm, ?_, l' + m', Submodule.add_mem _ hl' hm', ?_, ?_⟩
  · have := (Xsp F).add_mem h1 k1
    rwa [show x - l + (y - m) = x + y - (l + m) by abel] at this
  · have := (Xsp F').add_mem h2 k2
    rwa [show x - l' + (y - m') = x + y - (l' + m') by abel] at this
  · have := Submodule.add_mem _ h3 k3
    rwa [show l - l' + (m - m') = l + m - (l' + m') by abel] at this

/- English proof (translation)
Take `⟨l, hl, h1, l', hl', h2, h3⟩` from `hx`. Use `⟨o • l, Submodule.smul_mem _ o hl, ?_, o • l', Submodule.smul_mem _ o hl', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_sub]`. Conclude with `(toO S (Xsp F)).smul_mem o h1`. Rewrite using `[← smul_sub]`.

Conclude with `(toO S (Xsp F')).smul_mem o h2`. Rewrite using `[← smul_sub]`. Conclude with `Submodule.smul_mem _ o h3`.
-/
theorem IotaRel_smul {F : LFlag S r T} {F' : LFlag S r T'} {x : S.V} (o : 𝓞 E)
    (hx : IotaRel Λ g F F' x) : IotaRel Λ g F F' (o • x) := by
  obtain ⟨l, hl, h1, l', hl', h2, h3⟩ := hx
  refine ⟨o • l, Submodule.smul_mem _ o hl, ?_, o • l', Submodule.smul_mem _ o hl', ?_, ?_⟩
  · rw [← smul_sub]
    exact (toO S (Xsp F)).smul_mem o h1
  · rw [← smul_sub]
    exact (toO S (Xsp F')).smul_mem o h2
  · rw [← smul_sub]
    exact Submodule.smul_mem _ o h3

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact hx.2`. Consider the case `zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, IotaRel_zero F F'⟩`. Consider the case `add y z _ _ h1 h2`. Conclude with `⟨Submodule.add_mem _ h1.1 h2.1, Submodule.add_mem _ h1.2.1 h2.2.1, IotaRel_add h1.2.2 h2.2.2⟩`.

Consider the case `smul c y _ h`. Conclude with `⟨Submodule.smul_mem _ c h.1, Submodule.smul_mem _ c h.2.1, IotaRel_smul c h.2.2⟩`.
-/
theorem La_props {F : LFlag S r T} {F' : LFlag S r T'} {x : S.V} (hx : x ∈ La Λ g F F') :
    x ∈ L0sub Λ F ∧ x ∈ L0sub Λ F' ∧ IotaRel Λ g F F' x := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx.2
  | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, IotaRel_zero F F'⟩
  | add y z _ _ h1 h2 =>
    exact ⟨Submodule.add_mem _ h1.1 h2.1, Submodule.add_mem _ h1.2.1 h2.2.1, IotaRel_add h1.2.2 h2.2.2⟩
  | smul c y _ h =>
    exact ⟨Submodule.smul_mem _ c h.1, Submodule.smul_mem _ c h.2.1, IotaRel_smul c h.2.2⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `Submodule.mem_inf.1 hl`. Use `Submodule.mem_inf.2 ⟨(FrEqv.aut_mem_iff hβ l).2 h1, ?_⟩` and prove the remaining obligations. Use `mem_orth.2 fun u hu => ?_` and prove the remaining obligations. Rewrite `hu` using `[← hX]`. Take `⟨v, hv, rfl⟩` from `hu`.

Use `hβ.1 v l` as an intermediate fact. Conclude with `this.trans (mem_orth.1 h2 v hv)`.
-/
theorem map_Lrep {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V} (hβ : IsAutLam S Λ β)
    (hX : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'') {l : S.V} (hl : l ∈ Lrep Λ F') :
    β l ∈ Lrep Λ F'' := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hl
  refine Submodule.mem_inf.2 ⟨(FrEqv.aut_mem_iff hβ l).2 h1, ?_⟩
  refine mem_orth.2 fun u hu => ?_
  rw [← hX] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have := hβ.1 v l
  exact this.trans (mem_orth.1 h2 v hv)

/- English proof (translation)
Take `⟨hβ, hfl, hz, hc⟩` from `hP`. Establish `hX : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F''`. Rewrite using `[X_eq_Xflag F', X_eq_Xflag F'']`. Conclude with `hfl r`. Introduce `x₁ hx`.

Take `⟨hLa, hTh⟩` from `Submodule.mem_inf.1 hx`. Take `⟨h0, h0', l, hl, hxl, l', hl', hxl', hll⟩` from `La_props hLa`. Establish `hz1 : S.hT F.fl.z x₁ = 0` using `(Submodule.mem_inf.1 h0).2`. Establish `hz1' : S.hT F'.fl.z x₁ = 0` using `(Submodule.mem_inf.1 h0').2`. Take `⟨⟨a, x₂⟩, hp, he⟩` from `(Submodule.restrictScalars_mem _ _ _).1 hTh`.

Establish `hax : a = x₁` using `he`. Substitute `hax` using the available equality. Take `⟨⟨hprod, h12⟩, hβ12⟩` from `Submodule.mem_inf.1 hp |>.imp_left Submodule.mem_inf.1`. Establish `hx₂ : x₂ ∈ Hp Λ F F''` using `hprod.2`. Establish `h12 : a - x₂ ∈ Xsp F` using `h12`.

Establish `hβ12 : β a - x₂ ∈ Xsp F''` using `hβ12`. Establish `hβl : β l' ∈ Lrep Λ F''` using `map_Lrep hβ hX hl'`. Establish `hβd : β (a - l') ∈ Xsp F''`. Rewrite using `[← hX]`. Conclude with `⟨a - l', hxl', rfl⟩`.

Establish `k1 : x₂ - l ∈ Xsp F`. Use `(Xsp F).sub_mem hxl h12` as an intermediate fact. Rewrite `this` using `[show a - l - (a - x₂) = x₂ - l by abel]`. Then use the resulting hypothesis. Establish `k2 : x₂ - β l' ∈ Xsp F''`. Use `(Xsp F'').sub_mem hβd hβ12` as an intermediate fact.

Rewrite `this` using `[map_sub, show β a - β l' - (β a - x₂) = x₂ - β l' by abel]`. Then use the resulting hypothesis. Establish `m1 : S.hT F.fl.z x₂ = 0`. Use `hT_z_X F h12` as an intermediate fact. Rewrite `this` using `[map_sub, hz1, zero_sub, neg_eq_zero]`. Conclude with `this`.

Establish `m2 : S.hT F''.fl.z x₂ = 0`. Use `hT_z_X F'' hβ12` as an intermediate fact. Rewrite `this` using `[map_sub, ← hz, hβ.1 F'.fl.z a, hz1', zero_sub, neg_eq_zero, hz]`. Conclude with `this`. Establish `hmem : x₂ ∈ La Λ g F F''`.

Use `Submodule.subset_span ⟨hx₂, Submodule.mem_inf.2 ⟨mem_Lsub_of hl k1, m1⟩, Submodule.mem_inf.2 ⟨mem_Lsub_of hβl k2, m2⟩, l, hl, k1, β l', hβl, k2, ?_⟩` and prove the remaining obligations. Conclude with `(hc l' hl' l hl).1 hll`. Establish `hsum : a = x₂ + (a - x₂)` using `by abel`. Rewrite using `[hsum]`. Conclude with `Submodule.add_mem_sup hmem h12`.
-/
theorem Mlat_le_La_sup (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hP : IsPair Λ F F' F'' β g) : Mlat Λ F F' F'' β g ≤ La Λ g F F'' ⊔ toO S (Xsp F) := by
  obtain ⟨hβ, hfl, hz, hc⟩ := hP
  have hX : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'' := by
    rw [X_eq_Xflag F', X_eq_Xflag F'']
    exact hfl r
  intro x₁ hx
  obtain ⟨hLa, hTh⟩ := Submodule.mem_inf.1 hx
  obtain ⟨h0, h0', l, hl, hxl, l', hl', hxl', hll⟩ := La_props hLa
  have hz1 : S.hT F.fl.z x₁ = 0 := (Submodule.mem_inf.1 h0).2
  have hz1' : S.hT F'.fl.z x₁ = 0 := (Submodule.mem_inf.1 h0').2
  obtain ⟨⟨a, x₂⟩, hp, he⟩ := (Submodule.restrictScalars_mem _ _ _).1 hTh
  have hax : a = x₁ := he
  subst hax
  obtain ⟨⟨hprod, h12⟩, hβ12⟩ := Submodule.mem_inf.1 hp |>.imp_left Submodule.mem_inf.1
  have hx₂ : x₂ ∈ Hp Λ F F'' := hprod.2
  have h12 : a - x₂ ∈ Xsp F := h12
  have hβ12 : β a - x₂ ∈ Xsp F'' := hβ12
  have hβl : β l' ∈ Lrep Λ F'' := map_Lrep hβ hX hl'
  have hβd : β (a - l') ∈ Xsp F'' := by
    rw [← hX]
    exact ⟨a - l', hxl', rfl⟩
  have k1 : x₂ - l ∈ Xsp F := by
    have := (Xsp F).sub_mem hxl h12
    rwa [show a - l - (a - x₂) = x₂ - l by abel] at this
  have k2 : x₂ - β l' ∈ Xsp F'' := by
    have := (Xsp F'').sub_mem hβd hβ12
    rwa [map_sub, show β a - β l' - (β a - x₂) = x₂ - β l' by abel] at this
  have m1 : S.hT F.fl.z x₂ = 0 := by
    have := hT_z_X F h12
    rw [map_sub, hz1, zero_sub, neg_eq_zero] at this
    exact this
  have m2 : S.hT F''.fl.z x₂ = 0 := by
    have := hT_z_X F'' hβ12
    rw [map_sub, ← hz, hβ.1 F'.fl.z a, hz1', zero_sub, neg_eq_zero, hz] at this
    exact this
  have hmem : x₂ ∈ La Λ g F F'' := by
    refine Submodule.subset_span ⟨hx₂, Submodule.mem_inf.2 ⟨mem_Lsub_of hl k1, m1⟩,
      Submodule.mem_inf.2 ⟨mem_Lsub_of hβl k2, m2⟩, l, hl, k1, β l', hβl, k2, ?_⟩
    exact (hc l' hl' l hl).1 hll
  have hsum : a = x₂ + (a - x₂) := by abel
  rw [hsum]
  exact Submodule.add_mem_sup hmem h12

end GlobalTheory.LoopC.PairLat

end
