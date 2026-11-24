module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0421
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0363
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsAdmissibleKernelScheme
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumSymmetricTranslatesThetaPullbackExtends
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometriesObj
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links

namespace GlobalTheory.AdIsomObj

theorem adelicIsometries_obj (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.AdelicIsometries D :=
  GlobalTheory.AdIsom.adelicIsometries D

theorem frames_exist (D : D7) (V : HSp D) (N : ℕ) : ∃ β Λ, IsSDFrame V β Λ N :=
  (adelicIsometries_obj D).2.2.2.2.2.2.2.2.2.2.2.1 V N

end GlobalTheory.AdIsomObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowBplus

open GlobalTheory.Per GlobalTheory.Per.Inhab
open scoped Pointwise

variable {D : D7}

theorem integrable_of_haar {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E}
    {Q : GA D A → GA D B → ℂ} (hQ : IsRatInv ι e Q) (he : IsIsoSub B e) (hι : HSpace.IsIsomEmb A B ι) (hA : IsAniso A)
    (hc : Continuous fun q : GA D A × NFlag B e => Q q.1 q.2) {μ : Measure (GA D A)} {𝓕 : Set (GA D A)}
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 μ) {ν : Measure (NFlag B e)} {𝓝 : Set (NFlag B e)}
    (hN : IsUnitN B e ν 𝓝) :
    (∀ g, IntegrableOn (fun n : NFlag B e => Q g n) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, Q g n ∂ν) 𝓕 μ := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A hA
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B _ _ he).1
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  haveI := hμ
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ A) hK hcov μ h𝓕
  obtain ⟨M, hM⟩ := (hK.prod hK').exists_bound_of_continuousOn hc.continuousOn
  refine FJConv.iterated_integrableOn hfin.ne (by rw [hN.2.2]; exact ENNReal.one_ne_top) hc (M := M) fun g n => ?_
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov g
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨_, hQ.norm _ γ⁻¹ ((hs _ _).2 rfl) n n.2⟩
  have e' : s γ⁻¹ * n * (s γ⁻¹)⁻¹ = (γ' : GA D B) * k' := congrArg Subtype.val e
  have e1 : (n : GA D B) = s γ * (γ' * k') * (s γ)⁻¹ := by
    rw [← e']; simp only [map_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  refine le_trans (le_of_eq ?_) (hM (k, k') ⟨hk, hk'⟩)
  rw [e1, hQ.conj k _ (mul_mem γ'.2 k'.2) γ hγ _ ((hs _ _).2 rfl), hQ.left k _ k'.2 _ γ'.2 hγ']

theorem isAutFun_star {V : HSp D} {φ : GA D V → ℂ} (h : IsAutFun V φ) : IsAutFun V (star φ) := by
  obtain ⟨U, hU, hUφ⟩ := h.level
  exact ⟨fun γ hγ g => by simp only [Pi.star_apply, h.left γ hγ g],
    ⟨U, hU, fun k hk hkf g => by simp only [Pi.star_apply, hUφ k hk hkf g]⟩, h.cont.star⟩

section Col

open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols levPlus mem_cols)

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (θ : InfFam D)

theorem coefPlus_fin {h : GA D (G.V (.top 0))} (hh : h ∈ GfC (G.V (.top 0))) : (coefPlus G θ).ρ h = 1 := by
  have e : GlobalTheory.CoefModel.realGL θ (Xp G) h = 1 := funext fun τ => by
    show Formalism.UG.bc (θ τ) (infHom (Xp G) h) = 1
    rw [show infHom (Xp G) h = 1 from hh, map_one]
  show GlobalTheory.CoefModel.rhoH _ _ (invTrK (GlobalTheory.CoefModel.realGL θ (Xp G) h)) = 1
  rw [e, map_one, map_one]

theorem coefPlus_cont (hθ : IsInfFam θ) (x : (coefPlus G θ).W) : Continuous fun h => (coefPlus G θ).ρ h x := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  refine GlobalTheory.CoefModel.continuous_rhoH _ _ (fun h => invTrK (GlobalTheory.CoefModel.realGL θ (Xp G) h)) (fun τ => ?_) x
  refine (((GlobalTheory.CoefModel.realGL_laws hθ (Xp G)).1 τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
  show Matrix.transpose (GlobalTheory.CoefModel.realGL θ (Xp G) h⁻¹ τ : Matrix (Fin (Xp G).rank) (Fin (Xp G).rank) ℂ) = _
  rw [map_inv]
  rfl

theorem rho_cancel (ξ : Module.Dual ℂ (coefPlus G θ).W) (x : (coefPlus G θ).W) (γ g : GA D (G.V (.top 0))) :
    ξ ((coefPlus G θ).ρ (γ * g)⁻¹ ((coefPlus G θ).ρ γ x)) = ξ ((coefPlus G θ).ρ g⁻¹ x) := by
  have key : (coefPlus G θ).ρ (γ * g)⁻¹ * (coefPlus G θ).ρ γ = (coefPlus G θ).ρ g⁻¹ := by
    rw [← MonoidHom.map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  rw [← Module.End.mul_apply, key]

theorem rho_right (ξ : Module.Dual ℂ (coefPlus G θ).W) (x : (coefPlus G θ).W) (k g : GA D (G.V (.top 0)))
    (hk : (coefPlus G θ).ρ k⁻¹ = 1) :
    ξ ((coefPlus G θ).ρ (g * k)⁻¹ x) = ξ ((coefPlus G θ).ρ g⁻¹ x) := by
  rw [mul_inv_rev, MonoidHom.map_mul (coefPlus G θ).ρ k⁻¹ g⁻¹, Module.End.mul_apply, hk, Module.End.one_apply]

theorem col_right {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W} (hΨ : Ψ ∈ Cols G θ) (g : GA D (G.V (.top 0)))
    {k : GA D (G.V (.top 0))} (hk : k ∈ (G.Kplus).comap (Lev.finE (G.V (.top 0)))) :
    Ψ ((finHom (G.V (.top 0))).rangeRestrict (g * k)) = Ψ ((finHom (G.V (.top 0))).rangeRestrict g) := by
  have hk2 : (finHom (G.V (.top 0))).rangeRestrict k ∈ levPlus G := by
    rw [Subgroup.mem_comap] at hk
    rw [levPlus, Subgroup.mem_comap, Lev.toAfE, Subgroup.mem_comap]
    exact hk
  have h1 := (mem_cols G θ Ψ).1 hΨ 1 ((finHom (G.V (.top 0))).rangeRestrict g) ⟨_, hk2⟩
  simp only [map_one, one_mul, OneMemClass.coe_one, Module.End.one_apply] at h1
  rw [map_mul]; exact h1

theorem pairVec_left (ξ : Module.Dual ℂ (coefPlus G θ).W) {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W}
    (hΨ : Ψ ∈ Cols G θ) {γ : GA D (G.V (.top 0))} (hγ : γ ∈ GQ (G.V (.top 0))) (g : GA D (G.V (.top 0))) :
    pairVec (coefPlus G θ) ξ Ψ (γ * g) = pairVec (coefPlus G θ) ξ Ψ g := by
  rw [pairVec_apply, pairVec_apply]
  have h1 := (mem_cols G θ Ψ).1 hΨ ⟨γ, hγ⟩ ((finHom (G.V (.top 0))).rangeRestrict g) 1
  simp only [OneMemClass.coe_one, mul_one] at h1
  have e1 : (finHom (G.V (.top 0))).rangeRestrict (γ * g) =
      Bridge.ratF (G.V (.top 0)) ⟨γ, hγ⟩ * (finHom (G.V (.top 0))).rangeRestrict g := map_mul _ _ _
  rw [e1, h1]
  exact rho_cancel G θ ξ _ γ g

theorem pairVec_right (ξ : Module.Dual ℂ (coefPlus G θ).W) {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W}
    (hΨ : Ψ ∈ Cols G θ) {k : GA D (G.V (.top 0))} (hk : k ∈ (G.Kplus).comap (Lev.finE (G.V (.top 0))))
    (hkf : k ∈ GfC (G.V (.top 0))) (g : GA D (G.V (.top 0))) :
    pairVec (coefPlus G θ) ξ Ψ (g * k) = pairVec (coefPlus G θ) ξ Ψ g := by
  rw [pairVec_apply, pairVec_apply, col_right G θ hΨ g hk]
  exact rho_right G θ ξ _ k g (coefPlus_fin G θ (inv_mem hkf))

theorem pairVec_cont (hθ : IsInfFam θ) (ξ : Module.Dual ℂ (coefPlus G θ).W)
    {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W} (hΨ : Ψ ∈ Cols G θ) :
    Continuous (pairVec (coefPlus G θ) ξ Ψ) := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  have hU := (congLev_open_compact (G.V (.top 0)) (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hV.sd) (G.pl.modul_ne_bot sc)).1
  refine continuous_iff_continuousAt.2 fun h0 => ?_
  have hn : h0 • (((G.Kplus).comap (Lev.finE (G.V (.top 0))) : Subgroup _) : Set (GA D (G.V (.top 0)))) ∈ nhds h0 :=
    (hU.leftCoset h0).mem_nhds ⟨1, one_mem _, mul_one h0⟩
  have hev : (fun h => pairVec (coefPlus G θ) ξ Ψ h) =ᶠ[nhds h0]
      fun h => ξ ((coefPlus G θ).ρ h⁻¹ (Ψ ((finHom (G.V (.top 0))).rangeRestrict h0))) := by
    filter_upwards [hn] with h hh
    obtain ⟨k, hk, rfl⟩ := hh
    rw [pairVec_apply]
    simp only [smul_eq_mul]
    rw [col_right G θ hΨ h0 hk]
  refine ContinuousAt.congr ?_ hev.symm
  exact ((LinearMap.continuous_of_finiteDimensional ξ).comp ((coefPlus_cont G θ hθ _).comp continuous_inv)).continuousAt

theorem pairVec_isAutFun (hθ : IsInfFam θ) (ξ : Module.Dual ℂ (coefPlus G θ).W)
    {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W} (hΨ : Ψ ∈ Cols G θ) :
    IsAutFun (G.V (.top 0)) (pairVec (coefPlus G θ) ξ Ψ) := by
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  exact ⟨fun γ hγ g => pairVec_left G θ ξ hΨ hγ g,
    ⟨_, (congLev_open_compact (G.V (.top 0)) (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hV.sd) (G.pl.modul_ne_bot sc)).1,
      fun k hk hkf g => pairVec_right G θ ξ hΨ hk hkf g⟩, pairVec_cont G θ hθ ξ hΨ⟩

end Col

theorem bplusConv_col : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (_hM : M.IsRow) (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W)
    (Ψ : Bridge.Gf (G.V (.top 0)) → (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W) (_hΨ : Ψ ∈ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.Cols G W.θ)
    (F : GA D (G.V (.grid D.R.m 0)) → ℂ) (_hF : IsAutFun (G.V (.grid D.R.m 0)) F),
    BplusConv W M (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ) ξ Ψ) F := by
  intro D T L sc G W M hM ξ Ψ hΨ F hF
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  have hA : IsAniso (G.V (.top 0)) := GlobalTheory.Per.isAniso_of_posDef hV.sigOK fun τ => by
    rw [hV.sig τ, hV.rank]; simp [Node.neg]
  have hφ := isAutFun_star (pairVec_isAutFun G W.θ W.θ_is ξ hΨ)
  have hι := (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have hs : ∀ h, EmbRel _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι (embTop G h) h :=
    fun h => (embRel_iff _ h _).2 rfl
  have hQ : IsRatInv (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι G.besTop.e
      (fun h n => star (star (pairVec _ ξ Ψ) h) * F (n * embTop G h * (G.besTop.y : GA D _)) *
        star (besChar W.ψ G.besTop n)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro δ γ h n hn
      exact (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop δ γ h n hn).1
    · intro g n hn γ hγ hq
      rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop γ n hγ hn,
        GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop γ hγ hq, one_mul,
        mul_assoc γ, mul_assoc γ, hF.left γ hq]
    · intro g n hn γ hγ δ hδ
      obtain ⟨s₀, -, hrel, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _ hι
      have he : embTop G = s₀ := funext fun h => (hrel h _).1 (hs h)
      have hc : F (δ * n * δ⁻¹ * embTop G (γ * g) * G.besTop.y) =
          F (n * embTop G g * G.besTop.y) := by
        rw [he, (hrel _ _).1 hδ, ← hF.left _ (hq γ hγ) (n * s₀ g * G.besTop.y)]
        simp only [map_mul, mul_assoc, inv_mul_cancel_left]
      rw [(GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop δ γ hδ n hn).2, hc, hφ.left γ hγ]
  obtain ⟨hμ, h𝓕⟩ := hM.top.haar_fund
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m 0))
  have H := integrable_of_haar hQ G.besTop.e_iso hι hA
    (((hφ.cont.comp continuous_fst).star.mul (hF.cont.comp (((continuous_subtype_val.comp continuous_snd).mul
      ((emb_continuous hι hs).comp continuous_fst)).mul continuous_const))).mul
      ((GlobalTheory.BesselChar.besChar_continuous W.ψ W.ψ_std.1 G.besTop).comp continuous_snd).star) hμ h𝓕 hM.unip
  unfold BplusConv
  rw [besInt_eq]
  exact H

end GlobalTheory.RowBplus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.BrRat

open MvPolynomial _root_.Formalism.L2.Col Formalism.L2.Ker

section General

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem projVV_of_mem {K : Type} [Field K] [CharZero K] (sg : ι → DomWeight n) (x : VV K sg) :
    Br.projVV sg x.1 = x := by
  have h := GlobalTheory.Proof.TensorMapDescent.eq_zero_of_fockB sg (Br.projVV sg x.1 - x) fun i => by
    rw [← fockBL_apply, Submodule.coe_sub, map_sub, fockBL_apply, fockBL_apply,
      GlobalTheory.Proof.TensorMapDescent.fockB_projVV_basis, sub_self]
  exact sub_eq_zero.mp h

theorem exists_map_eq {K : Type} [Field K] (φ : K →+* ℂ) {σ : Type} (P : MvPolynomial σ ℂ)
    (h : ∀ m, AddMonoidAlgebra.coeff P m ∈ Set.range φ) : ∃ P₀ : MvPolynomial σ K, map φ P₀ = P := by
  classical
  choose c hc using h
  refine ⟨∑ m ∈ P.support, monomial m (c m), ?_⟩
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_monomial, hc]

theorem descend {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (sg : ι → DomWeight n) (x : VV ℂ sg)
    (h : ∀ m, AddMonoidAlgebra.coeff x.1 m ∈ Set.range φ) : ∃ y : VV K sg, map φ y.1 = x.1 := by
  obtain ⟨P₀, hP⟩ := exists_map_eq φ x.1 h
  refine ⟨Br.projVV sg P₀, ?_⟩
  rw [← GlobalTheory.Proof.TensorMapDescent.projVV_map φ sg P₀, hP, projVV_of_mem]

theorem map_frDet {K : Type} [Field K] (φ : K →+* ℂ) (τ : ι) : map φ (frDet K n τ) = frDet ℂ n τ := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext a s
  simp

theorem map_dualSubst {K : Type} [Field K] (φ : K →+* ℂ) (P : Pol K ι n) :
    map φ (dualSubst K ι n P) = dualSubst ℂ ι n (map φ P) := by
  have e : (map φ : Pol K ι n →+* Pol ℂ ι n).comp (dualSubst K ι n).toRingHom =
      (dualSubst ℂ ι n).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [dualSubst]
    · intro v
      have hm : (Matrix.of fun a s : Fin n => (X (v.1, a, s) : Pol ℂ ι n)) =
          (map φ : Pol K ι n →+* Pol ℂ ι n).mapMatrix (Matrix.of fun a s : Fin n => (X (v.1, a, s) : Pol K ι n)) := by
        ext a s
        simp
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, dualSubst, aeval_X, map_X]
      rw [hm, ← RingHom.map_adjugate]
      rfl
  exact DFunLike.congr_fun e P

theorem isFunForm_map {K : Type} [Field K] (φ : K →+* ℂ) (σ : ι → DomWeight n) {F : VV K σ}
    {f : VV K fun τ => (σ τ).dual} (h : IsFunForm σ F f) :
    IsFunForm σ ⟨map φ F.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ σ _ F.2⟩
      ⟨map φ f.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ _ _ f.2⟩ := by
  unfold IsFunForm at h ⊢
  have h1 := congrArg (map φ) h
  simp only [map_mul, map_prod, map_pow, map_frDet, map_dualSubst] at h1
  exact h1

theorem covOf_eq (σ : ι → DomWeight n) (f : VV ℂ fun τ => (σ τ).dual) : covOf σ f = (funEquiv σ).symm f := by
  have hex : ∃ φ : (VV ℂ fun τ => (σ τ).dual) →ₗ[ℂ] VV ℂ σ, ∀ f, IsFunForm σ (φ f) f :=
    ⟨(funEquiv σ).symm.toLinearMap, fun f => (isFunForm_iff_eq σ _ f).2 (by simp)⟩
  have e : covOf σ f = hex.choose f := by rw [covOf, dite_eq_left hex]
  rw [e]
  apply (funEquiv σ).injective
  rw [LinearEquiv.apply_symm_apply]
  exact ((isFunForm_iff_eq σ _ f).1 (hex.choose_spec f)).symm

theorem covOf_desc {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (σ : ι → DomWeight n)
    (f : VV ℂ fun τ => (σ τ).dual) (hf : ∀ m, AddMonoidAlgebra.coeff f.1 m ∈ Set.range φ) :
    ∃ F₀ : VV K σ, map φ F₀.1 = (covOf σ f).1 := by
  obtain ⟨f₀, hf₀⟩ := descend φ _ f hf
  refine ⟨(funEquiv σ).symm f₀, ?_⟩
  have h1 : IsFunForm σ ((funEquiv σ).symm f₀) f₀ := by
    have := isFunForm_funEquiv σ ((funEquiv σ).symm f₀)
    rwa [LinearEquiv.apply_symm_apply] at this
  have h2 := isFunForm_map φ σ h1
  have h4 : f = funEquiv σ ⟨map φ ((funEquiv σ).symm f₀).1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ σ _ ((funEquiv σ).symm f₀).2⟩ := by
    rw [← (isFunForm_iff_eq σ _ _).1 h2]
    exact Subtype.ext hf₀.symm
  rw [covOf_eq, h4, LinearEquiv.symm_apply_apply]

theorem brPair_mem_range {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (σ : ι → DomWeight n) {N : ℕ}
    (hN : N = n + 1) (Λ : ι → DomWeight N) (U : VV ℂ Λ) (V : VV ℂ fun τ => (σ τ).dual)
    (hU : ∀ m, AddMonoidAlgebra.coeff U.1 m ∈ Set.range φ) (hV : ∀ m, AddMonoidAlgebra.coeff V.1 m ∈ Set.range φ) :
    brPair σ hN Λ U V ∈ Set.range φ := by
  obtain ⟨U₀, hU₀⟩ := exists_map_eq φ U.1 hU
  obtain ⟨F₀, hF₀⟩ := covOf_desc φ σ V hV
  refine ⟨(extNormB K σ)⁻¹ * fockB (Br.brStdP hN Λ σ U₀ : Pol K ι n) F₀.1, ?_⟩
  rw [brPair, LinearMap.compl₁₂_apply, pairBK_apply, pairB_apply, ← hF₀, Br.brStd, LinearMap.comp_apply,
    Submodule.subtype_apply, ← hU₀, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map, GlobalTheory.Proof.TensorMapDescent.fockB_map, map_mul, map_inv₀]
  congr 2
  unfold extNormB
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]

end General

end GlobalTheory.BrRat

namespace GlobalTheory.RowClaim

theorem brPair_mem_coefField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ (U : VV ℂ (wt ch.G (.top D.R.m))) (V : VV ℂ (wt ch.G (.grid D.R.m D.R.m))), (∀ m, AddMonoidAlgebra.coeff U.1 m ∈ Set.range D.what₂.embLL) → (∀ m, AddMonoidAlgebra.coeff V.1 m ∈ Set.range D.what₂.embLL) → brPair (listedWt ch.G (.grid D.R.m D.R.m)) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) U V ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ _ t Φ _ U V hU hV
  haveI : CharZero D.what₂.LL := (RingHom.charZero_iff D.what₂.embLL.injective).mpr inferInstance
  exact GlobalTheory.BrRat.brPair_mem_range D.what₂.embLL _ _ _ U V hU hV

end GlobalTheory.RowClaim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateUnitaryAdelicIsoMapHaarFundamentalDomai
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.HaarConjImage

theorem map_isHaarFD : ∀ (D : D7) (S : HSp D) (c : D.host.E) {J : Matrix (Fin S.rank) (Fin S.rank) D.host.E} (hJ : J = c • S.gram), c ≠ 0 →
    ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), IsHaarFD S ν 𝓕 →
      (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ '' 𝓕)
        (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)) := by
  intro D S c J hJ hc ν 𝓕 h
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig S.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig S.gram
  have : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) := ⟨rfl⟩
  have c1 : Continuous (GlobalTheory.HaarConj.conjE S c hc hJ) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU S c hJ
  have c2 : Continuous (GlobalTheory.HaarConj.conjE S c hc hJ).symm := GlobalTheory.HaarConj.continuous_conjInv S c hc hJ
  haveI := h.1
  exact ⟨MulEquiv.isHaarMeasure_map ν (GlobalTheory.HaarConj.conjE S c hc hJ) c1 c2,
    GlobalTheory.HaarConj.isFundamentalDomain_image (GlobalTheory.HaarConj.conjE S c hc hJ) c1.measurable c2.measurable (GQ S) _
      (GlobalTheory.HaarConj.mem_ratU_iff S c hc hJ) ν 𝓕 h.2⟩

end GlobalTheory.HaarConjImage

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEtaleCoverListingHeckeKernelScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

theorem exists_etale_cover_lists_kerScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo P p i), admitted l P p → ∀ (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk), ∃ (T' : Type) (_ : CommRing T') (_ : Algebra T T') (n : ℕ) (σ : Fin n → (Sp T' ⟶ Xo.univ.t.G.left)), Algebra.Etale T T' ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap T T')) ∧ (∀ j, σ j ≫ Xo.univ.t.G.hom = spMap (algebraMap T T') ≫ h ≫ Z.π₁) ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T' →+* Ω) (x₁ : Sp Ω ⟶ Xo.X) (C : Subgroup (Over.mk x₁ ⟶ Xo.univ.t.G)), Z.Carries (spMap χ ≫ spMap (algebraMap T T') ≫ h) x₁ C → ∃ e : Fin n ≃ C, ∀ j, (e j).1.left = spMap χ ≫ σ j := by
  intro E _ _ _ H Dw l Xo P p i Z hA T _ h
  haveI := Z.isReduced
  obtain ⟨S', π, o', m, τ, hfin, het, hsur, hL⟩ :=
    GlobalTheory.exists_cover_lists_heckeSet E H Dw l P p i Z.Hk (Z.π₁ ≫ Xo.s) Z.o₁ Z.K hA Z.et Z.hecke
  obtain ⟨B, _, _, h', -, hBet, hh', hBsur, -⟩ := exists_finiteEtale_algebra_pullback Z.Hk S' π hfin het T h
  have wτ : ∀ a, (τ a).left ≫ o'.t.G.hom = 𝟙 S' := fun a => by simpa using Over.w (τ a)
  have wm : m.toSABMap.φ ≫ Z.o₁.t.G.hom = o'.t.G.hom ≫ π := m.cart.1.w
  have wm₁ : Z.m₁.toSABMap.φ ≫ Xo.univ.t.G.hom = Z.o₁.t.G.hom ≫ Z.π₁ := Z.m₁.cart.1.w
  have key : ∀ (X : Scheme.{0}) (w : X ⟶ S') a, (w ≫ (τ a).left ≫ m.toSABMap.φ) ≫ Z.o₁.t.G.hom = w ≫ π := by
    intro X w a
    rw [Category.assoc, Category.assoc, wm, reassoc_of% (wτ a)]; simp
  refine ⟨B, inferInstance, inferInstance, _, fun j => h' ≫ (τ j).left ≫ m.toSABMap.φ ≫ Z.m₁.toSABMap.φ, hBet,
    hBsur hsur, fun j => ?_, ?_⟩
  · have := congrArg (· ≫ Z.π₁) (key _ h' j)
    simp only [Category.assoc] at this
    simp only [Category.assoc, wm₁, this, reassoc_of% hh']
  intro Ω _ _ χ x₁ C hC
  obtain ⟨hz, hC⟩ := hC
  subst hz
  have hw' : (spMap χ ≫ h') ≫ π = spMap χ ≫ spMap (algebraMap T B) ≫ h := by rw [Category.assoc, hh']
  have hq : ∀ a, (spMap χ ≫ h' ≫ (τ a).left ≫ m.toSABMap.φ ≫ Z.m₁.toSABMap.φ) ≫ Xo.univ.t.G.hom =
      (spMap χ ≫ spMap (algebraMap T B) ≫ h) ≫ Z.π₁ := fun a => by
    have := congrArg (· ≫ Z.π₁) (key _ (spMap χ ≫ h') a)
    simp only [Category.assoc] at this hw'
    simp only [Category.assoc, wm₁, this, reassoc_of% hw']
  have mem : ∀ a, (Over.homMk (spMap χ ≫ h' ≫ (τ a).left ≫ m.toSABMap.φ ≫ Z.m₁.toSABMap.φ) (hq a) :
      Over.mk ((spMap χ ≫ spMap (algebraMap T B) ≫ h) ≫ Z.π₁) ⟶ Xo.univ.t.G) ∈ C := by
    intro a
    have hu := (key _ (spMap χ ≫ h') a).trans hw'
    refine (hC (Over.homMk ((spMap χ ≫ h') ≫ (τ a).left ≫ m.toSABMap.φ) hu) _ (by simp)).1 ?_
    rintro _ ⟨q, rfl⟩
    have h1 : ((spMap χ ≫ h') ≫ (τ a).left) q ∈ m.toSABMap.φ ⁻¹' Z.K := by
      rw [hL.2.1]
      exact Set.mem_iUnion.2 ⟨a, _, (Scheme.Hom.comp_apply _ _ _).symm⟩
    simpa [Scheme.Hom.comp_apply] using h1
  let f : Fin _ → C := fun a => ⟨_, mem a⟩
  have inj : Function.Injective f := by
    intro a b hab
    have e := congrArg (fun z : C => z.1.left) hab
    simp only [f, Over.homMk_left] at e
    refine hL.2.2 Ω (spMap χ ≫ h') ?_
    refine m.cart.1.hom_ext ?_ (by simp only [Category.assoc, wτ, Category.comp_id])
    refine Z.m₁.cart.1.hom_ext ?_ ?_
    · simpa only [Category.assoc] using e
    · simpa only [Category.assoc] using (key _ (spMap χ ≫ h') a).trans (key _ (spMap χ ≫ h') b).symm
  have surj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    have vw : v.left ≫ Xo.univ.t.G.hom = (spMap χ ≫ spMap (algebraMap T B) ≫ h) ≫ Z.π₁ := Over.w v
    let u₀ : Sp Ω ⟶ Z.o₁.t.G.left := Z.m₁.cart.1.lift v.left (spMap χ ≫ spMap (algebraMap T B) ≫ h) vw
    have u₀₁ : u₀ ≫ Z.m₁.toSABMap.φ = v.left := Z.m₁.cart.1.lift_fst _ _ _
    have u₀₂ : u₀ ≫ Z.o₁.t.G.hom = spMap χ ≫ spMap (algebraMap T B) ≫ h := Z.m₁.cart.1.lift_snd _ _ _
    have rK : Set.range u₀ ⊆ Z.K := (hC (Over.homMk u₀ u₀₂) v u₀₁.symm).2 hv
    let u₁ : Sp Ω ⟶ o'.t.G.left := m.cart.1.lift u₀ (spMap χ ≫ h') (u₀₂.trans hw'.symm)
    have u₁₁ : u₁ ≫ m.toSABMap.φ = u₀ := m.cart.1.lift_fst _ _ _
    have u₁₂ : u₁ ≫ o'.t.G.hom = spMap χ ≫ h' := m.cart.1.lift_snd _ _ _
    have q : Sp Ω := IsLocalRing.closedPoint Ω
    have hq1 : u₁ q ∈ m.toSABMap.φ ⁻¹' Z.K := by
      show (u₁ ≫ m.toSABMap.φ) q ∈ Z.K
      rw [u₁₁]; exact rK ⟨q, rfl⟩
    rw [hL.2.1] at hq1
    obtain ⟨a, g, hg⟩ := Set.mem_iUnion.1 hq1
    have := o'.proper
    have : IsClosedImmersion (τ a).left := by
      have hw : (τ a).left ≫ o'.t.G.hom = 𝟙 _ := Over.w _
      have : IsClosedImmersion ((τ a).left ≫ o'.t.G.hom) := by rw [hw]; infer_instance
      exact IsClosedImmersion.of_comp _ o'.t.G.hom
    obtain ⟨c, hc⟩ := GlobalTheory.HkFam.IndexZero.lift_closed (T := Sp Ω) u₁ (τ a).left (by
      rintro _ ⟨q', rfl⟩
      rw [Subsingleton.elim q' q]
      exact ⟨g, hg⟩)
    have hc' : c = spMap χ ≫ h' := by
      rw [← u₁₂, ← hc, Category.assoc, wτ]; simp
    refine ⟨a, Subtype.ext (Over.OverMorphism.ext ?_)⟩
    simp only [f, Over.homMk_left]
    rw [← u₀₁, ← u₁₁, ← hc, hc']
    simp only [Category.assoc]
  exact ⟨(Equiv.ofBijective f ⟨inj, surj⟩), fun j => rfl⟩

end GlobalTheory.HeckeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumSymmetricTranslatesThetaPullbackExtendsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_symmetricTranslates_thetaPullback_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (M : ℕ) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))), (∃ U : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, U.TorsionIso) → IsUnit (M : T.V) → letI := io.toAlgebra; IsTranslSum M y.1.s t → Reg I M t := by
  first | exact @GlobalTheory.HkIntegral.RegSum.reg_of_isTranslSum | exact GlobalTheory.HkIntegral.RegSum.reg_of_isTranslSum | (intros; apply GlobalTheory.HkIntegral.RegSum.reg_of_isTranslSum <;> assumption)
end

