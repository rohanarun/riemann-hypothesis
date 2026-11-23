module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.Bundle0004
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.UnipotentAdelicQuotients.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CauchyBinet.WwCauchyBinetMain
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
public import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Formalism.LocalToGlobal.Columns.HeckeInertComm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
public import Formalism.LocalToGlobal.HermitianForms.Bundle0003
public import Formalism.LocalToGlobal.Columns.RecLevelLocT

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyFamOk
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix

section

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}


omit [NumberField K] [StarRing K] in
theorem GStep.lsh_eq_map (S : GStep E K n) (h : S.Ok) (b : S.β) (g : S.G b) (d : S.D b) :
    S.Lsh b (g • d) = (S.Lsh b d).map
      ((Matrix.mulVecLin (S.gam b g : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E)) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  have e : (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ (((S.gam b g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y = y := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  constructor
  · intro hy
    exact ⟨_, (h.lsh_smul b g d _).1 (by rw [e]; exact hy), e⟩
  · rintro ⟨x, hx, rfl⟩
    exact (h.lsh_smul b g d x).2 hx


omit [StarRing K] [Fintype ι] in
theorem GStep.tauLat_smul (S : GStep E K n) (h : S.Ok) (emb : ι → E →+* K) [Fintype ι] (b : S.β) (g : S.G b) (d : S.D b) (τ : ι) :
    tauLat emb τ (S.Lsh b (g • d)) = gLat (embGL emb (S.gam b g) τ) (tauLat emb τ (S.Lsh b d)) := by
  rw [S.lsh_eq_map h]
  exact tauLatG E K ι n emb τ _ (S.gam b g)

end

theorem fam_ok : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n),
    FOk emb σ → S.Ok → (S.fam emb lam).Ok := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF h b
  have hr : ∀ g : S.G b, ∃ m : ℕ, 0 < m ∧ ((S.chr b g : Kˣ) : K) ^ m = 1 := fun g => by
    obtain ⟨m, hm, hc⟩ := h.root b g
    exact ⟨m, hm, by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]⟩
  refine ⟨h.fin_orb b, h.fin_stab b, ?_, ?_, ?_⟩
  · intro g d
    obtain ⟨m, hm, hc⟩ := hr g
    refine Eq.trans ?_ (map_root_smul _ (rhoVr emb lam (S.gam b g)) hm hc).symm
    show nabAtr emb lam (S.Lsh b (g • d)) = (nabAtr emb lam (S.Lsh b d)).map _
    unfold nabAtr
    simp_rw [S.tauLat_smul h emb b g d, dualFr_gLat]
    exact nabK_gLat lam _ (invTrK (embGL emb (S.gam b g)))
  · intro g d
    obtain ⟨m, hm, hc⟩ := hr g
    refine Eq.trans ?_ (map_root_smul _ (rhoVr emb lam (S.gam b g)) hm hc).symm
    show delAtr emb lam (S.Lsh b (g • d)) = (delAtr emb lam (S.Lsh b d)).map _
    unfold delAtr
    simp_rw [S.tauLat_smul h emb b g d, dualFr_gLat]
    exact delK_gLat lam _ (invTrK (embGL emb (S.gam b g)))
  · intro g x y
    obtain ⟨m, hm, hc⟩ := hr g
    have hU : S.gam b g ∈ Formalism.UG.UJ (starRingEnd E) (1 : Matrix (Fin n) (Fin n) E) := by
      have := h.unit b g
      show _ * _ * _ = _
      rw [Matrix.mul_one]
      exact this
    have hi : pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) (rhoVr emb lam (S.gam b g) x) (rhoVr emb lam (S.gam b g) y) =
        pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) x y :=
      pairInv K ι n lam _ _ (fun τ => (uJUnitary E K ι n emb (starRingEnd E) τ
        (fun x => (hF.emb_star τ x).symm) 1 _ hU).2 (by simp)) x y
    show pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) (((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) x)
      (((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) y) = pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hi, smul_smul]
    show (star ((S.chr b g : Kˣ) : K) * _) • _ = _
    rw [star_mul_root ⟨σ, hF.sig_star⟩ hm hc, one_smul]

end GlobalTheory.Mem.Col2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyLawBasis
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms

section General

variable {K : Type} [Field K] (σ : K →+* ℂ) {V W C J : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]

theorem li_pi_of_basis [Finite C] [Fintype J] (e : Module.Basis J K V) (ev : V →ₛₗ[σ] W)
    (he : LinearIndependent ℂ fun j => ev (e j)) {κ : Type} (b : κ → C → V) (hb : LinearIndependent K b) :
    LinearIndependent ℂ fun i => fun c => ev (b i c) := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  let r : (C → V) →ₗ[K] (C × J → K) :=
    LinearMap.pi fun p => (e.coord p.2) ∘ₗ LinearMap.proj p.1
  have hr : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    funext c
    apply e.ext_elem
    intro j
    simpa [r] using congrFun hf (c, j)
  have h1 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 (hb.map' r hr)
  let T : (C × J → ℂ) →ₗ[ℂ] (C → W) :=
    LinearMap.pi fun c => ∑ j, (LinearMap.proj (c, j) : (C × J → ℂ) →ₗ[ℂ] ℂ).smulRight (ev (e j))
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    funext p
    have h2 : ∑ j, u (p.1, j) • ev (e j) = 0 := by
      simpa [T, LinearMap.sum_apply] using congrFun hu p.1
    exact Fintype.linearIndependent_iff.1 he (fun j => u (p.1, j)) h2 p.2
  have h3 := h1.map' T hT
  suffices hs : (fun i => fun c => ev (b i c)) = T ∘ fun i => algebraMap K ℂ ∘ (r ∘ b) i by
    rw [hs]
    exact h3
  funext i c
  have h4 : b i c = ∑ j, e.repr (b i c) j • e j := (e.sum_repr _).symm
  conv_lhs => rw [h4]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ]
  simp [T, r, LinearMap.sum_apply, RingHom.algebraMap_toAlgebra]

theorem mem_span_basis_image [Fintype J] (e : Module.Basis J K V) (ev : V →ₛₗ[σ] W) (x : V) :
    ev x ∈ Submodule.span ℂ (Set.range fun j => ev (e j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← e.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem rho_sum_translates {G : Type} [Group G] [Fintype G] (ρ : G →* Module.End K V) (g : G) (x : V) :
    ρ g (∑ t, ρ t x) = ∑ t, ρ t x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun t => ?_
  simp [map_mul]

end General

namespace GStep

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)


omit [StarRing E] [StarRing K] in
theorem evV_rho_eq_tr (b : S.β) (g : S.G b) (F : VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g F) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ F) := by
  funext y
  have h1 : S.rho emb lam b g F = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) F := rfl
  rw [h1, LinearMap.map_smulₛₗ, tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb _ lam σ _ F y _ ?_
  have h2 : y = frMul emb σ (S.gam b g) (frMul emb σ (S.gam b g)⁻¹ y) := by
    rw [← frMul_mul, mul_inv_cancel, frMul_one]
  intro τ
  exact congrFun (congrArg Subtype.val h2) τ

theorem lawBasis_of_ok (h : (S.fam emb lam).Ok) : S.LawBasis emb σ lam h := by
  classical
  haveI : Fintype S.Cl := h.fintypeCl
  constructor
  · have h1 : LinearIndependent K fun a => ((S.csd emb lam h).basis a).1 :=
      (S.csd emb lam h).basis.linearIndependent.map' (S.csd emb lam h).Forms.subtype (Submodule.ker_subtype _)
    exact li_pi_of_basis σ (C := S.Cl) (S.csd emb lam h).bV (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ)
      (evV_linearIndependent emb _ lam σ (fr0 emb σ n) _ (S.csd emb lam h).bV.linearIndependent) _ h1
  · refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩ c
      refine ⟨evV_mem_ValC emb _ lam σ _, fun g => ?_⟩
      have h1 := ((S.csd emb lam h).basis a).2 c g
      have h2 := S.evV_rho_eq_tr emb σ lam c.1 g.1 (((S.csd emb lam h).basis a).1 c)
      exact h2.symm.trans (congrArg (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ) h1)
    · intro φ hφ
      rw [← Finset.univ_sum_single φ]
      refine Submodule.sum_mem _ fun c _ => ?_
      letI : Fintype (S.Stab c) := (S.csd emb lam h).finGam c
      let A : (Fr emb σ n → ℂ) →ₗ[ℂ] (S.Cl → Fr emb σ n → ℂ) :=
        LinearMap.single ℂ (fun _ : S.Cl => Fr emb σ n → ℂ) c ∘ₗ ∑ g : S.Stab c, (S.tr emb σ c.1 g.1).toLinearMap
      have hA : ∀ w, A w = Pi.single c (∑ g : S.Stab c, S.tr emb σ c.1 g.1 w) := fun w => by
        simp [A, LinearMap.sum_apply]
      have hle : ValC (Gr emb σ n) lam ≤ (Submodule.span ℂ
          (Set.range fun a => S.embF emb σ lam h ((S.hlat emb lam h).b a))).comap A := by
        rw [← span_evV, Submodule.span_le]
        rintro _ ⟨F, rfl⟩
        let ρc : S.Stab c →* Module.End K (VV K lam) :=
          (S.rho emb lam c.1).comp (MulAction.stabilizer (S.G c.1) (S.rep c)).subtype
        let x : S.FormsK emb lam h := ⟨(Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam), by
          intro c' γ
          by_cases hc : c' = c
          · subst hc
            show ρc γ ((Pi.single c' (∑ t, ρc t F) : S.Cl → VV K lam) c') =
              (Pi.single c' (∑ t, ρc t F) : S.Cl → VV K lam) c'
            rw [Pi.single_eq_same]
            exact rho_sum_translates ρc γ F
          · show S.rho emb lam c'.1 γ.1 ((Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c') =
              (Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c'
            rw [Pi.single_eq_of_ne hc, map_zero]⟩
        have hx : A (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ F) = S.embF emb σ lam h x := by
          rw [hA]
          funext c'
          show _ = evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ ((Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c')
          by_cases hc : c' = c
          · subst hc
            set_option synthInstance.maxHeartbeats 100000 in
              rw [Pi.single_eq_same, Pi.single_eq_same, map_sum]
            exact Finset.sum_congr rfl fun g _ => (S.evV_rho_eq_tr emb σ lam c'.1 g.1 F).symm
          · rw [Pi.single_eq_of_ne hc, Pi.single_eq_of_ne hc, map_zero]
        rw [SetLike.mem_coe, Submodule.mem_comap, hx]
        exact mem_span_basis_image σ (S.hlat emb lam h).b (S.embF emb σ lam h) x
      have h1 := Submodule.mem_comap.1 (hle (hφ c).1)
      have h2 : A (φ c) = (Fintype.card (S.Stab c) : ℂ) • (Pi.single c (φ c) : S.Cl → Fr emb σ n → ℂ) := by
        rw [hA, Finset.sum_congr rfl fun g _ => (hφ c).2 g, Finset.sum_const, Finset.card_univ, ← Pi.single_smul',
          Nat.cast_smul_eq_nsmul]
      rw [h2] at h1
      exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)).1 h1

end GStep

theorem lawBasis_all : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n),
    FOk emb σ → S.Ok → ∀ h, S.LawBasis emb σ lam h :=
  fun S emb σ lam _ _ h => S.lawBasis_of_ok emb σ lam h

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncreasingRowChoicePerColumn
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

abbrev IncreasingRowChoicePerColumn (N : ℕ) (Y : YoungDiagram) : Type := ∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N

def sig {Lt : Type} (N : ℕ) (s : Lt) : Fin N × Fin N → Lt × ℕ × Fin N := fun v => (s, (v.2 : ℕ), v.1)

theorem map_nablaX {Lt : Type} [Fintype Lt] (K : Type) [CommRing K] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (J : WeylLatticeDuality.ColChoice N nu) :
    map (Int.castRingHom K) (WeylLatticeDuality.nablaX N nu J) =
      ∏ s, rename (sig N s) (GlobalTheory.WeylMinorDual.colProd K N (nu s) (hY s) (J s)) := by
  unfold WeylLatticeDuality.nablaX GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext1 p q
  simp [sig]

theorem colLen_le_of_rowLen {N : ℕ} {Y : YoungDiagram} (h : Y.rowLen N = 0) : Y.colLen 0 ≤ N := by
  by_contra hc'
  have hc := not_le.mp hc'
  have h1 : (N, 0) ∈ Y := YoungDiagram.mem_iff_lt_colLen.mpr hc
  have h2 := YoungDiagram.mem_iff_lt_rowLen.mp h1
  omega

end GlobalTheory.WeylLatDualProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertPathCardCommLatticePathsStatement
section
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPath_card_comm_latticePaths : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}, (∀ R : ST, R.1 ≠ P) → (∀ w : SG, w.1 ≠ P) →
  ∀ (s t : List ℕ) (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)),
    Nonempty ({Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s d.1.N Y ∧ IsInertNbr P.asIdeal t Y f.1.N} ≃
      {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t d.1.N Y ∧ IsInertNbr P.asIdeal s Y f.1.N}) →
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card =
      ((d.inertNb P.asIdeal t).filter fun e => f ∈ e.inertNb P.asIdeal s).card := by
  first | exact @GlobalTheory.inertPath_card_comm | exact GlobalTheory.inertPath_card_comm | (intros; apply GlobalTheory.inertPath_card_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFundamentalDomainEqSumDoubleCosetAvg
section
open MeasureTheory

namespace GlobalTheory

open scoped Pointwise

theorem setIntegral_isFundamentalDomain_comp_mul_right {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) :
    ∫ x in 𝓕, f (x * g) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have h2 : IsFundamentalDomain Γ (MulOpposite.op g • 𝓕) μ := h𝓕.smul_of_comm (MulOpposite.op g)
  have himg : MulOpposite.op g • 𝓕 = (fun x => x * g) '' 𝓕 := by
    ext y; simp [Set.mem_smul_set, MulOpposite.smul_eq_mul_unop]
    constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro hy; exact ⟨_, hy, by simp⟩
  rw [← (measurePreserving_mul_right μ g).setIntegral_image_emb (measurableEmbedding_mulRight g) f 𝓕,
    ← himg]
  refine h2.setIntegral_eq h𝓕 ?_
  intro γ x
  rw [Subgroup.smul_def, smul_eq_mul]
  exact hf γ γ.2 x

theorem integral_fundamentalDomain_eq_sum_doubleCoset_avg : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ K Kf : Subgroup G) [Countable Γ] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → IsOpen (K : Set G) → μ K ≠ ⊤ → ∀ (U : Type) [Group U] [TopologicalSpace U] [IsTopologicalGroup U] [CompactSpace U] [MeasurableSpace U] [BorelSpace U] (ν : Measure U) [ν.IsMulLeftInvariant] [IsProbabilityMeasure ν] (j : U →* G), Continuous j → (∀ k ∈ K, ∃ k' ∈ Kf, ∃ w, k = k' * j w) → (∀ k ∈ Kf, ∀ w, k * j w = j w * k) → ∀ (ι : Type) [Fintype ι] (h : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k) → (∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite) → ∀ f : G → ℂ, Continuous f → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ k ∈ Kf, ∀ x, f (x * k) = f x) → IntegrableOn f 𝓕 μ ∧ ∫ x in 𝓕, f x ∂μ = ((μ K).toReal : ℂ) * ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ℕ) : ℂ)⁻¹ * ∫ v, f (h i * j v) ∂ν := by
  intro G _ _ _ _ _ _ μ _ _ Γ K Kf _ 𝓕 h𝓕 hK hKfin U _ _ _ _ _ _ ν _ _ j hj hdec hcomm ι _ h huniq
    hfin f hf hfl hfr
  have key : ∀ x, ∀ k' ∈ Kf, ∀ w, f (x * (k' * j w)) = f (x * j w) := by
    intro x k' hk' w
    rw [hcomm k' hk' w, ← mul_assoc, hfr k' hk']
  have hbd : ∃ C, ∀ x, ‖f x‖ ≤ C := by
    have hi : ∀ i, ∃ C, ∀ v, ‖f (h i * j v)‖ ≤ C := fun i =>
      (isCompact_range ((hf.comp (continuous_const.mul hj)).norm)).bddAbove.imp
        fun C hC v => hC ⟨v, rfl⟩
    choose B hB using hi
    refine ⟨∑ i, |B i|, fun x => ?_⟩
    obtain ⟨i, ⟨γ, hγ, k, hk, rfl⟩, -⟩ := huniq x
    obtain ⟨k', hk', w, rfl⟩ := hdec k hk
    rw [mul_assoc, hfl γ hγ, key _ k' hk' w]
    exact (hB i w).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |B i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨C, hC⟩ := hbd
  have hFl : ∀ γ ∈ Γ, ∀ x, ∫ v, f (γ * x * j v) ∂ν = ∫ v, f (x * j v) ∂ν := by
    intro γ hγ x
    congr 1; funext v; rw [mul_assoc, hfl γ hγ]
  have hFr : ∀ k ∈ K, ∀ x, ∫ v, f (x * k * j v) ∂ν = ∫ v, f (x * j v) ∂ν := by
    intro k hk x
    obtain ⟨k', hk', w, rfl⟩ := hdec k hk
    have e : ∀ v, f (x * (k' * j w) * j v) = f (x * j (w * v)) := by
      intro v
      have : x * (k' * j w) * j v = x * j (w * v) * k' := by
        calc x * (k' * j w) * j v = x * j w * (k' * j v) := by
                rw [hcomm k' hk' w]; simp only [mul_assoc]
          _ = x * j w * (j v * k') := by rw [hcomm k' hk' v]
          _ = x * j (w * v) * k' := by rw [map_mul]; simp only [mul_assoc]
      rw [this, hfr k' hk']
    simp_rw [e]
    exact integral_mul_left_eq_self (fun v => f (x * j v)) w
  obtain ⟨hfin𝓕, -, hFeq⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G μ Γ K 𝓕 h𝓕 hK
    hKfin ι h huniq hfin (fun x => ∫ v, f (x * j v) ∂ν) hFl hFr
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin𝓕
  have hint : IntegrableOn f 𝓕 μ :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  refine ⟨hint, ?_⟩
  have hc : Continuous fun p : G × U => f (p.1 * j p.2) :=
    hf.comp (continuous_fst.mul (hj.comp continuous_snd))
  have hI : Integrable (Function.uncurry fun x v => f (x * j v)) ((μ.restrict 𝓕).prod ν) :=
    Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hC _)
  calc ∫ x in 𝓕, f x ∂μ = ∫ x in 𝓕, ∫ v, f (x * j v) ∂ν ∂μ := by
        rw [integral_integral_swap hI]
        simp only [setIntegral_isFundamentalDomain_comp_mul_right μ Γ 𝓕 h𝓕 f hfl]
        simp
    _ = _ := hFeq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelActsTriviallyOnDiscriminantGroupStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_acts_trivially_on_discriminant_group : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (_ : ∀ x, σ (σ x) = x) {n : ℕ} [NeZero n] {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ (1 : Matrix (Fin n) (Fin n) E) T f bad) (p q : 𝓞 E) (_ : (q : E) = σ (p : E)) (_ : (p : E) * (q : E) = (T : E)) (_ : T ≠ 0)
    (_ : S.Lb = rll_dLat n ((p : E)⁻¹))
    (_ : Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb) = rll_dLat n (q : E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (_ : ∀ m : S.fM v hv, m ≠ 0 → ∀ d c : intV E v, (d - 1) • m = 0 →
      sigR σ (v.adicCompletion F) (d : E ⊗[F] v.adicCompletion F) * (d : E ⊗[F] v.adicCompletion F) =
        1 + (T : E ⊗[F] v.adicCompletion F) * (c : E ⊗[F] v.adicCompletion F) →
      ∃ e : intV E v, (d : E ⊗[F] v.adicCompletion F) = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F))
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (_ : x ∈ S.Uloc v),
    ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  first | exact @GlobalTheory.uloc_acts_trivially_on_dual_quotient | exact GlobalTheory.uloc_acts_trivially_on_dual_quotient | (intros; apply GlobalTheory.uloc_acts_trivially_on_dual_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexForms
section
noncomputable section

namespace GlobalTheory.Mem.Col2.DiaStab

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix

section General

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem tr_one (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  funext y
  simp [GStep.tr, trFr_apply, frMul_one]

theorem evV_rho (b : S.β) (g : S.G b) (v : VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g v) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) := by
  funext y
  have h : S.rho emb lam b g v = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) v := rfl
  rw [h, LinearMap.map_smulₛₗ, GStep.tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb 1 lam σ _ v y _ ?_
  have := congrArg Subtype.val ((frEquiv emb σ (S.gam b g)).apply_symm_apply y)
  intro τ
  exact (congrFun this τ).symm

theorem tr_mem (b : S.β) (g : S.G b)
    {F : Fr emb σ n → ℂ} (hF : F ∈ ValC (Gr emb σ n) lam) : S.tr emb σ b g F ∈ ValC (Gr emb σ n) lam := by
  rw [← span_evV emb 1 lam σ] at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [← evV_rho]
    exact evV_mem_ValC emb 1 lam σ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem mem_Fi (hf : S.Free)
    (φ : S.Cl → Fr emb σ n → ℂ) (h : ∀ c, φ c ∈ ValC (Gr emb σ n) lam) : φ ∈ S.Fi emb σ lam := fun c =>
  ⟨h c, fun g => by rw [hf c.1 g.1 _ g.2, tr_one]⟩

end General

theorem lawDiaStable : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R),
    FOk emb σ → ∀ (_hI : I.Ok), J.Ok → J.LawDiaStable emb σ hc := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc _ _ h
  rintro P a _ ⟨φ, hφ, rfl⟩
  exact mem_Fi _ emb σ _ h.free0 _ fun c => tr_mem _ emb σ _ _ _ (hφ _).1

end GlobalTheory.Mem.Col2.DiaStab
end
end

