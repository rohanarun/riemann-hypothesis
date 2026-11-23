module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.CuspAOfAb
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolOfUnr
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
open _root_.GlobalTheory GlobalTheory.WeilDeligne

namespace UpperTheory.GalS

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem inePol_of_unr {y : WD h} (u : y.unr) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) : y.inePol σ = (X - 1) ^ y.lpDim := by
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  rw [WD.unr_mk] at u
  rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.lpDim_mk, u.2 ⟨σ, hσ⟩, LinearMap.charpoly_one]

theorem NcW.of_unr {y : WD h} (u : y.unr) : NcW y := by
  refine ⟨fun σ hσ => inePol_of_unr u (GlobalTheory.TameEig.wild_mem_Ine B σ hσ), WD.unr_mono0 _ u, fun γ hγ _ z hz => ?_⟩
  rw [inePol_of_unr u hγ] at hz
  have h1 : ((X - 1 : ℂ[X]) ^ y.lpDim).IsRoot z := (rootMultiplicity_pos'.1 (lt_of_lt_of_le (thr_pos w) hz)).2
  have h2 : z - 1 = 0 := by
    simp only [IsRoot, eval_pow, eval_sub, eval_X, eval_one] at h1
    exact pow_eq_zero_iff (by rintro e; rw [e] at h1; simp at h1) |>.1 h1
  rw [sub_eq_zero.1 h2, one_pow]
end

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem nc_iff (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (y : A.LP w) : Nc N A y ↔ NcW (T.e w y) := by
  refine and_congr ⟨fun k σ hσ => ?_, fun k σ hσ hw => ?_⟩ (and_congr (T.mono0 w y)
    ⟨fun k γ hγ hc z hz => ?_, fun k γ hγ z hz => ?_⟩)
  · have hI := GlobalTheory.TameEig.wild_mem_Ine (E := H.E) _ σ hσ
    rw [← T.inePol w y σ hI, T.dim]
    exact k σ hI hσ
  · rw [T.inePol w y σ hσ, ← T.dim]
    exact k σ hw
  · exact k γ ⟨hγ, hc⟩ z (by rwa [T.inePol w y γ hγ, ← T.dim])
  · exact k γ hγ.1 hγ.2 z (by rwa [← T.inePol w y γ hγ.1, T.dim])

theorem ncW_of_nc (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {y : A.LP w} (h : Nc N A y) : NcW (T.e w y) := (nc_iff T y).1 h

theorem relW_of_aw (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h : Aw (T.e w x) (T.e w y)) : RelW N A x y := by
  refine ⟨by rw [← T.dim, ← T.dim, h.dim], fun u => (T.e w).injective (h.unr ((T.unr w y).1 u)), fun k σ hσ => ?_,
    fun k => (T.mono0 w x).2 (h.mono (ncW_of_nc T k))⟩
  rw [T.inePol _ _ σ hσ, T.inePol _ _ σ hσ, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ,
    h.ine (ncW_of_nc T k) _ (deg_ineIncl _)]

theorem cuspA_of_ab (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h1 : A.lpDim y ≠ 1)
    (h : UpperTheory.GalN.Ab (T.e w x) (T.e w y)) : UpperTheory.GalN.CuspA N A x y := UpperTheory.GalN.cuspA_of_ab T h1 h

end UpperTheory.GalS
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjAlt
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalStar

open UpperTheory.GalS (TmW)
open UpperTheory.GalN (SplW)

abbrev RecNotion : Type 1 :=
  ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w), (IrrGL (k := w.adicCompletion E) → WD h) → Prop

def IsQp {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def Tor (y : WD h) : Prop := ∀ s t : ↥(Weil h), LocalGlobalAboveLAlt.Triv y ⁅s, t⁆

def Sqf (y : WD h) : Prop :=
  ∀ γ ∈ Ine (F := E) A, ((Ine (F := E) A : Subgroup (G E Ω)) : Set (G E Ω)) ⊆
      closure ((Subgroup.closure (insert γ {σ : G E Ω | ∀ z : Ω, z ≠ 0 → A.valuation (σ z / z - 1) < 1}) : Subgroup (G E Ω)) :
        Set (G E Ω)) →
    ∀ z : ℂ, 2 ≤ (y.inePol γ).rootMultiplicity z → z ^ (normV w - 1) = 1

structure Away (x y : WD h) : Prop where
  dim : x.lpDim = y.lpDim

  tor : Tor y → y.mono0 → x = y

  tame0 : IsQp w → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g

structure AwayN (x y : WD h) : Prop where
  ine : IsQp w → TmW y → ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g
  spl : IsQp w → TmW y → ∀ (u : WD h) (c : G E Ω → ℂ) (t : ℕ), ∀ γ ∈ Ine (F := E) A,
    ((y.lpSum u).inePol γ).rootMultiplicity (c γ) ≤ t → SplW c t (y.lpSum u) → SplW c t (x.lpSum u)
end Local

variable (Rc : RecNotion) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

structure Above (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where
  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)

  nice : ∀ σ, π.IsLocComp w σ → ∀ rc, Rc h rc → ((IsQp w ∧ TmW (rc (algNorm σ)) ∧ Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ))) → (rc (algNorm σ)).mono0 →
    IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    (∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)) ∧
    Away (GlobalTheory.Pst.wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))

structure Props (π : CuspSub E a) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), Rc h rc → ∀ σ, π.IsLocComp w σ →
      Away (GlobalTheory.WeilDeligne.wdOf h hl ι r) (rc (algNorm σ))
  weights : ∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
    ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z
  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), Above Rc π ι r HT P h Bw hj

def TameN (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), Rc h rc → ∀ σ, π.IsLocComp w σ →
      AwayN (GlobalTheory.WeilDeligne.wdOf h hl ι r) (rc (algNorm σ))

def Row0 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), Props Rc π ι r wt HT

end UpperTheory.GalStar
end
end

