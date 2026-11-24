module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0059
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeVecSatakeSumUnitaryBorelRepresentatives
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SatBorel

theorem heckeVec_satU_borel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ), ∀ h ∈ Hecke ℂ (KU σ n), ∃ (ι : Type) (_ : Fintype ι) (b : ι → GU σ n), (∀ i, IsBorelU (b i)) ∧ (∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (GU σ n) M) (s : M), (∀ k ∈ KU σ n, π k s = s) → heckeVec π (KU σ n) h s = ∑ i, h (b i) • π (b i) s) ∧ ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q h (fun i => (α i : ℂ)) = ∑ i, h (b i) * ∏ k : Fin (n / 2), ((α k : ℂ) * (q : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k.1 : ℤ)))) ^ ordL ((b i).1.1 (lo n k) (lo n k)) := by
  intro L _ _ _ ϖ σ q hU n h hh
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hfin := P.finite_support_cosets hK hh.2
  have hI : ∀ c : GU σ n ⧸ KU σ n, ∃ b : GU σ n, IsBorelU b ∧ (b : GU σ n ⧸ KU σ n) = c := by
    intro c
    obtain ⟨b, k, hb, hk, e⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 c.out
    refine ⟨b, hb, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' c, e]
    exact QuotientGroup.eq.2 (by simpa using hk)
  choose s hsB hs using hI
  have hhs : ∀ c, h (s c) = h c.out := by
    intro c
    have hk : (c.out)⁻¹ * s c ∈ KU σ n := QuotientGroup.eq.1 (c.out_eq'.trans (hs c).symm)
    have e : s c = 1 * c.out * ((c.out)⁻¹ * s c) := by group
    rw [e]
    exact hh.1 1 ⟨_, hk⟩ c.out
  have c1 : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (GU σ n) M) (x : M),
      (∀ k ∈ KU σ n, π k x = x) →
      heckeVec π (KU σ n) h x = ∑ i : hfin.toFinset, h (s i.1) • π (s i.1) x := by
    intro M _ _ π x hx
    rw [GlobalTheory.LFun.heckeVec_eq_of_section hh.1 (GlobalTheory.LGrp.mem_fixed.2 hx) s hs,
      finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_, ← Finset.sum_coe_sort]
    intro c hc
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq, ← hhs]
    intro h0
    exact hc (by simp [h0])
  refine ⟨hfin.toFinset, inferInstance, fun i => s i.1, fun i => hsB _, c1, fun α => ?_⟩
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega)
    (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have e := congrFun (Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega) _
    (fun i => (α i).ne_zero) h hh φ hφ) 1
  have hfix : ∀ k ∈ KU σ n, GlobalTheory.PRep.rightReg ℂ (GU σ n) ℂ k φ = φ := by
    intro k hk
    funext g
    change φ (g * k) = φ g
    simpa [GlobalTheory.LFun.chiDeltaU_one] using hφ 1 g k GlobalTheory.LFun.isBorelU_one hk
  rw [← GlobalTheory.LFun.heckeVec_rightReg hK hh, c1 _ _ φ hfix] at e
  have hχ : ∀ i : hfin.toFinset, φ (s i.1) = ∏ k : Fin (n / 2),
      ((α k : ℂ) * (q : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k.1 : ℤ)))) ^ ordL ((s i.1).1.1 (lo n k) (lo n k)) := by
    intro i
    have := hφ (s i.1) 1 1 (hsB _) (one_mem _)
    simp only [mul_one, h1] at this
    rw [this]
    unfold chiDeltaU
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [dite_eq_left (by omega), mul_zpow, ← _root_.zpow_mul]
    have hl : lo n k = ⟨k.1, by omega⟩ := rfl
    rw [hl]
    congr 2
    ring
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h1, mul_one] at e
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hχ i]
  exact congrArg (h (s i.1) * ·) (congrArg φ (one_mul _))

end GlobalTheory.SatBorel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeZeroOrEmptyEqZero
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical

namespace GlobalTheory.HeisDerivZero

theorem evI_surj {F : Type} [Field F] [NumberField F] (y : mixedEmbedding.mixedSpace F) : ∃ a : AF F, evI F a = y :=
  ⟨((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y, 0), (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y⟩

theorem actsD_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (g h : SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hA : ActsD (evI F) (M.heisLine ψ u) g h) (hc : g = 0 ∨ IsEmpty (Fin n × Fin d)) : h = 0 := by
  have hR : Rest (evI F) g (fun _ => 1) := by
    refine ⟨fun _ _ _ => rfl, ?_⟩
    rcases hc with rfl | hE
    · have : tens (evI F) (⇑(0 : SInf F (Fin n × Fin d))) (fun _ => 1) = 0 := by
        funext x; simp [tens]
      rw [this]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨g, fun _ => 1, ⟨IsLocallyConstant.const 1, ?_⟩, rfl⟩
      exact HasCompactSupport.of_compactSpace _
  have hconst : ∀ t x, M.heisLine ψ u t (tens (evI F) g fun _ => 1) x = tens (evI F) g (fun _ => 1) x := by
    intro t x
    rcases hc with rfl | hE
    · simp [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, tens]
    · simp only [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, dotProduct, Finset.univ_eq_empty,
        Finset.sum_empty, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
      congr 1
      exact Subsingleton.elim _ _
  ext y
  choose x hx using fun i => evI_surj (F := F) (y i)
  have h1 := hA _ hR x
  simp only [hconst] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  simpa [tens, hx] using h2

end GlobalTheory.HeisDerivZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumUniqueOfSelfDual
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

theorem vacuum_unique_of_selfDual {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) (Λ : Submodule R X)
    (hΛ : SelfDual γ Λ) (s : M) (hs : s ≠ 0) (hfix : Fixes W Λ s)
    (hspan : Submodule.span ℂ (Set.range fun x => W x s) = ⊤) (v : M) (hv : Fixes W Λ v) : ∃ c : ℂ, v = c • s := by
  have key : ∀ z : X, W z s = (γ (w • (Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ) : X))
      (z - Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ)))⁻¹ • W (Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ)) s := by
    intro z
    set t : X := Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ) with ht
    have hmem : z - t ∈ Λ := by
      rw [← Submodule.Quotient.eq]
      exact (Quotient.out_eq (Submodule.Quotient.mk z : X ⧸ Λ)).symm
    have h1 := h.comp t (z - t) s
    rw [hfix _ hmem, add_sub_cancel] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ (h.ne_zero _ _), one_smul]
  have hli : LinearIndependent ℂ (fun q : X ⧸ Λ => W (Quotient.out q) s) := by
    refine linearIndependent_of_simultaneous_eigen _ (fun q (a : Λ) => γ a (Quotient.out q)) (fun a : Λ => W a) ?_ ?_ ?_
    · intro q q' hq
      have hm : (Quotient.out q : X) - Quotient.out q' ∈ Λ := by
        rw [hΛ]
        intro a ha
        apply h.swap_eq_one
        have h1 : γ a (Quotient.out q) = γ a (Quotient.out q') := congrFun hq ⟨a, ha⟩
        rw [sub_eq_add_neg, h.add_right, h.neg_right, h1, mul_inv_cancel₀ (h.ne_zero _ _)]
      rw [← Submodule.Quotient.eq] at hm
      have e1 : (Submodule.Quotient.mk (Quotient.out q) : X ⧸ Λ) = q := Quotient.out_eq q
      have e2 : (Submodule.Quotient.mk (Quotient.out q') : X ⧸ Λ) = q' := Quotient.out_eq q'
      rw [← e1, ← e2, hm]
    · intro a q
      rw [h.comm, hfix a a.2]
    · intro q h0
      have h1 := h.neg_comp (Quotient.out q) s
      rw [h0, map_zero] at h1
      exact hs ((smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _))
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun q : X ⧸ Λ => W (Quotient.out q) s) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    show W z s ∈ _
    rw [key z]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  let b := Module.Basis.mk hli hsp
  have hb : ∀ q, b q = W (Quotient.out q) s := fun q => Module.Basis.mk_apply hli hsp q
  have hcoord : ∀ a ∈ Λ, ∀ q x, b.coord q (W a x) = γ a (Quotient.out q) * b.coord q x := by
    intro a ha q x
    have e : (b.coord q).comp (W a) = γ a (Quotient.out q) • b.coord q := by
      refine b.ext fun q' => ?_
      rw [LinearMap.comp_apply, hb, h.comm, hfix a ha, ← hb, LinearMap.smul_apply, map_smul, smul_eq_mul]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul, Finsupp.single_apply]
      split_ifs with hq
      · rw [hq]
      · simp
    exact LinearMap.congr_fun e x
  have h0 : (Quotient.out (0 : X ⧸ Λ) : X) ∈ Λ :=
    (Submodule.Quotient.mk_eq_zero Λ).1 (Quotient.out_eq (0 : X ⧸ Λ))
  have hb0 : b 0 = s := by rw [hb, hfix _ h0]
  have hvan : ∀ q : X ⧸ Λ, q ≠ 0 → b.repr v q = 0 := by
    intro q hq
    have hn : (Quotient.out q : X) ∉ Λ := fun hm => hq (by
      have e1 : (Submodule.Quotient.mk (Quotient.out q) : X ⧸ Λ) = q := Quotient.out_eq q
      rw [← e1]; exact (Submodule.Quotient.mk_eq_zero Λ).2 hm)
    rw [hΛ] at hn
    push_neg at hn
    obtain ⟨a, ha, hne⟩ := hn
    have hne' : γ a (Quotient.out q) ≠ 1 := fun e => hne (h.swap_eq_one e)
    have e := hcoord a ha q v
    rw [hv a ha, Module.Basis.coord_apply] at e
    have e2 : (γ a (Quotient.out q) - 1) * b.repr v q = 0 := by rw [sub_mul, ← e]; ring
    exact (mul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 hne')
  refine ⟨b.repr v 0, b.ext_elem fun q => ?_⟩
  rw [map_smul, ← hb0, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases hq : (0 : X ⧸ Λ) = q
  · subst hq; simp
  · rw [if_neg hq, mul_zero, hvan q (Ne.symm hq)]

end GlobalTheory.SphTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompactOpenTypeIdempotentUnipotentEqZero
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.TypeIdemAverage

theorem integral_eq_zero_of_sum_translate {N ι : Type} [Group N] [MeasurableSpace N] [MeasurableMul N]
    (ν : Measure N) [ν.IsMulLeftInvariant] [Fintype ι] [Nonempty ι] (n : ι → N) (F : N → ℂ)
    (h : ∀ u, ∑ i, F (n i * u) = 0) : ∫ u, F u ∂ν = 0 := by
  by_cases hF : Integrable F ν
  · have h1 : ∫ u, ∑ i, F (n i * u) ∂ν = ∑ i, ∫ u, F (n i * u) ∂ν :=
      integral_finsetSum _ fun i _ => hF.comp_mul_left (n i)
    simp only [h, integral_zero, integral_mul_left_eq_self, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (by exact_mod_cast Fintype.card_ne_zero)
  · exact integral_undef hF

theorem sum_typeIdem_translate {G Q W : Type} [Group G] [MeasurableSpace G] (μ : Measure G) [Group Q]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {K : Subgroup G} (red : K →* Q)
    (τ : Representation ℂ Q W) (H : Subgroup Q) [Fintype H] (hH : NoFixed τ H) (κ : H → K)
    (hκ : ∀ v, red (κ v) = v) (g : G) : ∑ v, GlobalTheory.Orb.typeIdem μ red τ (κ v * g) = 0 := by
  by_cases hg : g ∈ K
  · obtain ⟨g, rfl⟩ : ∃ g' : K, (g' : G) = g := ⟨⟨g, hg⟩, rfl⟩
    have h0 := GlobalTheory.NoFixedCharSum.noFixedSum Q W τ H hH 1 (red g)
    simp only [← Subgroup.coe_mul, GlobalTheory.Orb.typeIdem_coe, map_mul red, hκ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.mul_sum, ← map_sum]
    simp only [one_mul] at h0
    have h1 : ∑ v : H, τ.character ((v : Q) * red g) = 0 := h0
    rw [h1, map_zero, mul_zero]
  · refine Finset.sum_eq_zero fun v _ => GlobalTheory.Orb.typeIdem_of_notMem μ red τ ?_
    rwa [K.mul_mem_cancel_left (κ v).2]

theorem integral_idemGL_eq_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {r : ℕ}
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W)
    [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k))
    (N : Subgroup (GL (Fin r) k)) (ν : Measure N) [ν.IsMulLeftInvariant] (H : Subgroup (GL (Fin r) 𝓀[k]))
    (hH : NoFixed τ H) (x : GL (Fin r) k)
    (hx : ∀ v ∈ H, ∃ n ∈ N, ∃ hn : x * n * x⁻¹ ∈ KO k (Fin r),
      GlobalTheory.LocGL.redK k (Fin r) ⟨x * n * x⁻¹, hn⟩ = v)
    (w : GL (Fin r) k) : ∫ u : N, idemGL k μ τ (x * u * w) ∂ν = 0 := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  choose n hnN hnK hred using hx
  refine integral_eq_zero_of_sum_translate ν (fun v : H => (⟨n v v.2, hnN v v.2⟩ : N))
    (fun u : N => idemGL k μ τ (x * u * w)) fun u => ?_
  have h := sum_typeIdem_translate μ (GlobalTheory.LocGL.redK k (Fin r)) τ H hH
    (fun v => ⟨x * n v v.2 * x⁻¹, hnK v v.2⟩) (fun v => hred v v.2) (x * u * w)
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) h
  simp only [idemGL, Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left]

end GlobalTheory.TypeIdemAverage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvTransposeInvTranspose
section
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace Matrix
open scoped TensorProduct

namespace GlobalTheory.LocalThetaGL

section Abstract

variable {H V W U Y Γ : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup Y] [Module ℂ Y] {P : Subgroup H}

end Abstract

section Regular

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] {π : Representation ℂ G V}

end Regular

section Local

open GlobalTheory.IndefiniteRowSideFullHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]

theorem compact_open_basis (n : Type) [Fintype n] [DecidableEq n] : ∀ U ∈ nhds (1 : GL n k),
    ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ IsCompact (K : Set (GL n k)) ∧ (K : Set (GL n k)) ⊆ U := by
  intro U hU
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k n U hU
  exact ⟨J, h1, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

end Local

section Main

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Published

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Main

section Final

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Published

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


end Final

end GlobalTheory.LocalThetaGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpMSelfEqZero
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvalAtUnitVector

theorem ipM_self_eq_zero {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T : MMap M) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (h0 : T v = 0) :
    ipM M μ 𝓕 T T = 0 := by
  by_cases h : ∃ c, IsMultIP M μ 𝓕 T T c
  · have h1 := (ipM_spec M μ 𝓕 T T h v v).2
    have h2 : (∏ τ, inner ℂ (v τ : M.H τ) (v τ : M.H τ)) = 1 :=
      Finset.prod_eq_one fun τ _ => by
        rw [inner_self_eq_norm_sq_to_K, hv τ]
        simp
    rw [h2, mul_one, h0] at h1
    rw [← h1]
    simp
  · unfold ipM
    exact dif_neg h

theorem evInj {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (he : R.models_HW)
    (hv : ∀ i σ, IsChosenExtremalVector R i σ (v₀ i σ)) : EvInj T R v₀ := by
  intro i σ _ x y hxy
  have h0 : (R.HW i σ).e (x - y) (v₀ i σ) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.2 hxy
  have h1 := (he i σ).2.2 (x - y) (x - y)
  rw [ipAt, ipM_self_eq_zero _ _ _ _ (v₀ i σ) (IsChosenExtremalVector.norm R (hv i σ)) h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

end GlobalTheory.EvalAtUnitVector
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLevelDatumEqFunctionOfResidueReductionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLevelDatum_eq_function_of_residueReduction : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b t : ℕ) (ht : a + t = b) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ)
    (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ), IsLocLevel φ PP L H c J lam →
    ∀ (mu : (Fv D.host.F v)ˣ →* ℂˣ) (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu χ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v),
      localNewformFunction v J lam mu (rowsTB ht Y) = viaRed r (gLoc (b := b) L PP H c χ) Y := by
  first | exact @GlobalTheory.StepVec.locDatum_eq_viaRed | exact GlobalTheory.StepVec.locDatum_eq_viaRed | (intros; apply GlobalTheory.StepVec.locDatum_eq_viaRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemStdMaxParabolicOfBlockParabolicLeConj
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

namespace GlobalTheory.ParabConj

theorem stdBlocks_lt {s r : ℕ} (d : Fin s → ℕ) (hd : ∑ i, d i = r) {a b : Fin s} (i : Fin (d a)) (j : Fin (d b))
    (hba : b < a) : stdBlocks d hd ⟨b, j⟩ < stdBlocks d hd ⟨a, i⟩ := by
  let f : ℕ → ℕ := fun n => if h : n < s then d ⟨n, h⟩ else 0
  have key : ∀ c : Fin s, ∑ x : Fin c, d (Fin.castLE c.2.le x) = ∑ x ∈ Finset.range c, f x := by
    intro c
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : (x : ℕ) < s := x.2.trans c.2
    simp only [f, hx, dif_pos]
    rfl
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, key, key]
  have h1 : ∑ x ∈ Finset.range (b + 1), f x ≤ ∑ x ∈ Finset.range a, f x :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hba))
  rw [Finset.sum_range_succ] at h1
  have h2 : f b = d b := by simp [f]
  have := j.2
  omega

theorem mem_stdMaxParab_of_le_conjBy (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ)
    (hd : ∑ i, d i = r) (g : GL (Fin r) F) (H : parab F (stdBlocks d hd) ≤ conjBy g (stdMaxParab F h)) :
    g ∈ stdMaxParab F h := by
  by_contra hg
  have hg' := hg
  rw [mem_stdMaxParab] at hg'
  push Not at hg'
  obtain ⟨q, j, hj, hq, hne⟩ := hg'
  refine hg (inv_mem_iff.1 ((mem_stdMaxParab h).2 fun i p hp hi => ?_))
  have hpq : p < q := by rw [Fin.lt_def]; omega
  let t : GL (Fin r) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection p q (1 : F))
    (by rw [Matrix.det_transvection_of_ne p q hpq.ne]; exact one_ne_zero)
  have ht : (t : Matrix (Fin r) (Fin r) F) = 1 + Matrix.single p q 1 := rfl
  have htP : t ∈ parab F (stdBlocks d hd) := by
    refine mem_parab_iff.2 fun x y u v hyx => ?_
    have hlt := stdBlocks_lt d hd u v hyx
    rw [ht, Matrix.add_apply, Matrix.one_apply_ne hlt.ne', zero_add]
    refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
    rintro ⟨e1, e2⟩
    rw [← e1, ← e2] at hlt
    exact lt_asymm hlt hpq
  have h0 := (mem_stdMaxParab h).1 (mem_conjBy.1 (H htP)) i j hj hi
  have hij : i ≠ j := by rintro rfl; omega
  have hmul : ((g⁻¹ * t * g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      1 + ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * Matrix.single p q (1 : F) *
        (g : Matrix (Fin r) (Fin r) F) := by
    rw [Units.val_mul, Units.val_mul, ht, mul_add, add_mul, mul_one, Units.inv_mul]
  rw [hmul, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add, Matrix.mul_apply,
    Finset.sum_eq_single q (fun x _ hx => by rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hx, zero_mul]) (by simp),
    Matrix.mul_single_apply_same, mul_one] at h0
  exact (mul_eq_zero.1 h0).resolve_right hne

end GlobalTheory.ParabConj
end

