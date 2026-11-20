import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlProps
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `x hx`. Rewrite using `[MonoidHom.mem_ker]`. Establish `key : ∀ k : ℕ, PadicInt.toZModPow k ((ε x : ℤ_[l])) = 1`. Introduce `k`. Set `χ : Γ →* (ZMod (l ^ k))ˣ` to `(Units.map (PadicInt.toZModPow k : ℤ_[l] →+* ZMod (l ^ k)).toMonoidHom).comp ε`.

Establish `hmemχ : ∀ g, g ∈ χ.ker ↔ (ε g : ℤ_[l]) ∈ Metric.closedBall (1 : ℤ_[l]) ((l : ℝ) ^ (-(k : ℤ)))`. Introduce `g`. Rewrite using `[MonoidHom.mem_ker, Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero, Units.ext_iff]`. Both sides reduce to the same expression. Establish `hopen : IsOpen (χ.ker : Set Γ)`.

Establish `hset : (χ.ker : Set Γ) = (fun g => (ε g : ℤ_[l])) ⁻¹' Metric.closedBall 1 ((l : ℝ) ^ (-(k : ℤ)))`. Use extensionality with `g`. Conclude with `hmemχ g`. Rewrite using `[hset]`. Conclude with `(IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero))).preimage (Units.continuous_val.comp hε)`.

Set `U : OpenNormalSubgroup Γ` to `⟨⟨χ.ker, hopen⟩, χ.normal_ker⟩`. Establish `hcond : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U`. Introduce `h hh`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use `show h ^ l ^ k ∈ χ.ker`.

Rewrite using `[hmemχ, map_pow, Units.val_pow_eq_pow_val, Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]`. Establish `hd : (l : ℤ_[l]) ∣ (ε h : ℤ_[l]) - 1`. Rewrite using `[← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, h1 h hh, sub_self]`. Establish `hp` using `dvd_sub_pow_of_dvd_sub hd k`. Rewrite `hp` using `[one_pow]`.

Conclude with `(pow_dvd_pow _ (Nat.le_succ k)).trans hp`. Establish `hle : PL l H ≤ (U.toOpenSubgroup : Subgroup Γ)`. Unfold `PL`. Conclude with `(iInf_le _ U).trans (iInf_le _ hcond)`. Establish `hxU : x ∈ χ.ker` using `hle hx`.

Rewrite `hxU` using `[MonoidHom.mem_ker]`. Establish `hv` using `congrArg Units.val hxU`. Simplify `hv` using `[χ]`. Conclude with `Units.ext (PadicInt.ext_of_toZModPow.mp (fun k => by rw [key k, Units.val_one, map_one]))`.
-/
private theorem pl_le_ker {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ)
    (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (h1 : ∀ a ∈ H, PadicInt.toZMod ((ε a : ℤ_[l]ˣ) : ℤ_[l]) = 1) :
    PL l H ≤ ε.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have key : ∀ k : ℕ, PadicInt.toZModPow k ((ε x : ℤ_[l])) = 1 := by
    intro k
    let χ : Γ →* (ZMod (l ^ k))ˣ :=
      (Units.map (PadicInt.toZModPow k : ℤ_[l] →+* ZMod (l ^ k)).toMonoidHom).comp ε
    have hmemχ : ∀ g, g ∈ χ.ker ↔
        (ε g : ℤ_[l]) ∈ Metric.closedBall (1 : ℤ_[l]) ((l : ℝ) ^ (-(k : ℤ))) := by
      intro g
      rw [MonoidHom.mem_ker, Metric.mem_closedBall, dist_eq_norm,
        PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
        map_one, sub_eq_zero, Units.ext_iff]
      rfl
    have hopen : IsOpen (χ.ker : Set Γ) := by
      have hset : (χ.ker : Set Γ) =
          (fun g => (ε g : ℤ_[l])) ⁻¹' Metric.closedBall 1 ((l : ℝ) ^ (-(k : ℤ))) := by
        ext g
        exact hmemχ g
      rw [hset]
      exact (IsUltrametricDist.isOpen_closedBall _
        (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero))).preimage
        (Units.continuous_val.comp hε)
    let U : OpenNormalSubgroup Γ := ⟨⟨χ.ker, hopen⟩, χ.normal_ker⟩
    have hcond : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U := by
      intro h hh
      refine ⟨k, ?_⟩
      show h ^ l ^ k ∈ χ.ker
      rw [hmemχ, map_pow, Units.val_pow_eq_pow_val, Metric.mem_closedBall, dist_eq_norm,
        PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
      have hd : (l : ℤ_[l]) ∣ (ε h : ℤ_[l]) - 1 := by
        rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
          RingHom.mem_ker, map_sub, map_one, h1 h hh, sub_self]
      have hp := dvd_sub_pow_of_dvd_sub hd k
      rw [one_pow] at hp
      exact (pow_dvd_pow _ (Nat.le_succ k)).trans hp
    have hle : PL l H ≤ (U.toOpenSubgroup : Subgroup Γ) := by
      unfold PL
      exact (iInf_le _ U).trans (iInf_le _ hcond)
    have hxU : x ∈ χ.ker := hle hx
    rw [MonoidHom.mem_ker] at hxU
    have hv := congrArg Units.val hxU
    simpa [χ] using hv
  exact Units.ext (PadicInt.ext_of_toZModPow.mp (fun k => by rw [key k, Units.val_one, map_one]))

/- English proof (translation)
Introduce `l _ L G H _ hH hη hε1`. Take `⟨hN, hC, hKH, -, -, -⟩` from `pl_props l G.Γ H hH`. Use `haveI := hN`. Set `π : G.Γ →* G.Γ ⧸ PL l H` to `QuotientGroup.mk' (PL l H)`. Establish `hπc : Continuous π` using `QuotientGroup.continuous_mk`.

Establish `hπs : Function.Surjective π` using `QuotientGroup.mk'_surjective _`. Establish `hπo : IsOpenMap π` using `QuotientGroup.isOpenMap_coe`. Establish `hπq : Topology.IsQuotientMap π` using `hπo.isQuotientMap hπc hπs`. Use `haveI : TotallyDisconnectedSpace (G.Γ ⧸ PL l H) := (totallyDisconnected_quot G.Γ _ hC).1`. Set `η' : G.Γ ⧸ PL l H →* ℤˣ` to `QuotientGroup.lift (PL l H) G.η (hKH.trans hη)`.

Set `ε' : G.Γ ⧸ PL l H →* ℤ_[l]ˣ` to `QuotientGroup.lift (PL l H) G.ε (pl_le_ker H G.ε G.ε_cont hε1)`. Establish `hηo : IsOpen (η'.ker : Set (G.Γ ⧸ PL l H))`. Establish `hset : (η'.ker : Set (G.Γ ⧸ PL l H)) = π '' (G.η.ker : Set G.Γ)`. Use extensionality with `y`. Take `⟨x, rfl⟩` from `hπs y`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `⟨x, hy, rfl⟩`. Introduce and unpack `⟨z, hz, hzx⟩ show η' (π x) = 1`. Rewrite using `[← hzx]`.

Conclude with `hz`. Rewrite using `[hset]`. Conclude with `hπo _ G.η_open`. Establish `hεc : Continuous ε'`. Rewrite using `[hπq.continuous_iff]`.

Conclude with `G.ε_cont`. Set `r : G.η.ker →* η'.ker` to `(π.comp G.η.ker.subtype).codRestrict η'.ker (fun x => by show η' (π x) = 1`. Conclude with `x.2)`. Establish `hrc : Continuous r` using `continuous_induced_rng.2 (hπc.comp continuous_subtype_val)`. Set `G' : Glob l L` to `{ Γ := G.Γ ⧸ PL l H η := η' η_open := hηo c := π G.c c_sq := by rw [← map_mul, G.c_sq, map_one] η_c := G.η_c ε := ε' ε_cont := hεc φ := fun v => r.comp (G.φ v) φ_cont := fun v => hrc.comp (G.φ_cont v) φu := fun u => r.comp (G.φu u) φu_cont := fun u => hrc.comp (G.φu_cont u) }`.

Use `⟨G', ⟨π, hπc, hπs, fun _ => rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, ?_⟩` and prove the remaining obligations. Conclude with `QuotientGroup.ker_mk' _`.
-/
theorem UpperTheory.V.Pa.quot_ex :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G : Glob l L) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (∀ a ∈ H, PadicInt.toZMod ((G.ε a : ℤ_[l]ˣ) : ℤ_[l]) = 1) → ∃ (G' : Glob l L) (g : G.Hom G'), g.p.ker = PL l H := by
  intro l _ L G H _ hH hη hε1
  obtain ⟨hN, hC, hKH, -, -, -⟩ := pl_props l G.Γ H hH
  haveI := hN
  let π : G.Γ →* G.Γ ⧸ PL l H := QuotientGroup.mk' (PL l H)
  have hπc : Continuous π := QuotientGroup.continuous_mk
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπo : IsOpenMap π := QuotientGroup.isOpenMap_coe
  have hπq : Topology.IsQuotientMap π := hπo.isQuotientMap hπc hπs
  haveI : TotallyDisconnectedSpace (G.Γ ⧸ PL l H) := (totallyDisconnected_quot G.Γ _ hC).1
  let η' : G.Γ ⧸ PL l H →* ℤˣ := QuotientGroup.lift (PL l H) G.η (hKH.trans hη)
  let ε' : G.Γ ⧸ PL l H →* ℤ_[l]ˣ :=
    QuotientGroup.lift (PL l H) G.ε (pl_le_ker H G.ε G.ε_cont hε1)
  have hηo : IsOpen (η'.ker : Set (G.Γ ⧸ PL l H)) := by
    have hset : (η'.ker : Set (G.Γ ⧸ PL l H)) = π '' (G.η.ker : Set G.Γ) := by
      ext y
      obtain ⟨x, rfl⟩ := hπs y
      constructor
      · intro hy
        exact ⟨x, hy, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        show η' (π x) = 1
        rw [← hzx]
        exact hz
    rw [hset]
    exact hπo _ G.η_open
  have hεc : Continuous ε' := by
    rw [hπq.continuous_iff]
    exact G.ε_cont
  let r : G.η.ker →* η'.ker :=
    (π.comp G.η.ker.subtype).codRestrict η'.ker (fun x => by
      show η' (π x) = 1
      exact x.2)
  have hrc : Continuous r := continuous_induced_rng.2 (hπc.comp continuous_subtype_val)
  let G' : Glob l L :=
    { Γ := G.Γ ⧸ PL l H
      η := η'
      η_open := hηo
      c := π G.c
      c_sq := by rw [← map_mul, G.c_sq, map_one]
      η_c := G.η_c
      ε := ε'
      ε_cont := hεc
      φ := fun v => r.comp (G.φ v)
      φ_cont := fun v => hrc.comp (G.φ_cont v)
      φu := fun u => r.comp (G.φu u)
      φu_cont := fun u => hrc.comp (G.φu_cont u) }
  refine ⟨G', ⟨π, hπc, hπs, fun _ => rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, ?_⟩
  exact QuotientGroup.ker_mk' _
