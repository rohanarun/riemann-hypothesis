module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0808

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta
open Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Polynomial GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem
open Formalism.IndefR.Bridge (IsDC SplitOff)
open scoped TensorProduct

namespace GlobalTheory.HeckeParts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Group

variable {G : Type} [Group G]

theorem sum_eq_of_isDC {J : Subgroup G} {x : G} {R R' : Finset G} (h : IsDC J x R) (h' : IsDC J x R') (F : G → ℂ)
    (hF : ∀ k ∈ J, ∀ g, F (g * k) = F g) (g : G) : ∑ γ ∈ R, F (g * γ) = ∑ γ ∈ R', F (g * γ) := by
  have ex : ∀ a ∈ R, ∃ b, b ∈ R' ∧ b⁻¹ * a ∈ J := fun a ha => (h'.2 a (h.1 a ha)).exists
  choose φ hφ hφJ using ex
  refine Finset.sum_bij φ hφ ?_ ?_ ?_
  · intro a ha a' ha' e
    refine (h.2 a (h.1 a ha)).unique ⟨ha, by simp⟩ ⟨ha', ?_⟩
    have h1 := hφJ a ha
    have h2 := hφJ a' ha'
    rw [← e] at h2
    have := J.mul_mem (J.inv_mem h2) h1
    simpa [mul_assoc] using this
  · intro b hb
    obtain ⟨a, ha, hab⟩ := (h.2 b (h'.1 b hb)).exists
    refine ⟨a, ha, (h'.2 a (h.1 a ha)).unique ⟨hφ a ha, hφJ a ha⟩ ⟨hb, ?_⟩⟩
    simpa using J.inv_mem hab
  · intro a ha
    rw [← hF _ (hφJ a ha) (g * φ a ha)]
    congr 1
    group

theorem isDC_of_local {J L : Subgroup G} {x : G} {R : Finset G} (hx : x ∈ L) (hR : ∀ γ ∈ R, γ ∈ L)
    (hs : ∀ k ∈ J, ∃ a ∈ J, ∃ b ∈ J, a ∈ L ∧ Commute x b ∧ k = a * b)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ J ⊓ L, ∃ k₂ ∈ J ⊓ L, γ = k₁ * x * k₂)
    (h2 : ∀ y : G, (∃ k₁ ∈ J ⊓ L, ∃ k₂ ∈ J ⊓ L, y = k₁ * x * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * y ∈ J ⊓ L) : IsDC J x R := by
  refine ⟨fun γ hγ => ?_, ?_⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := h1 γ hγ
    exact ⟨⟨k₁, hk₁.1⟩, ⟨k₂, hk₂.1⟩, e⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ha, b, hb, haL, hc, e⟩ := hs k₁ k₁.2
    obtain ⟨γ, ⟨hγ, hγJ⟩, hu⟩ := h2 (a * x) ⟨a, ⟨ha, haL⟩, 1, Subgroup.one_mem _, by simp⟩
    have eg : (k₁ : G) * x * k₂ = a * x * (b * k₂) := by
      rw [e, mul_assoc a b x, ← hc.eq]; group
    refine ⟨γ, ⟨hγ, ?_⟩, ?_⟩
    · rw [eg, ← mul_assoc]
      exact J.mul_mem hγJ.1 (J.mul_mem hb k₂.2)
    · rintro δ ⟨hδ, hδJ⟩
      refine hu δ ⟨hδ, ?_, L.mul_mem (L.inv_mem (hR δ hδ)) (L.mul_mem haL hx)⟩
      have := J.mul_mem hδJ (J.inv_mem (J.mul_mem hb k₂.2))
      rw [eg] at this
      simpa [mul_assoc] using this

end Group

theorem splitLab_pairwise (n k : ℕ) : (splitLab n k).Pairwise (fun a b => b ≤ a) := by
  unfold splitLab
  rw [List.pairwise_append]
  refine ⟨by simp [List.pairwise_replicate], by simp [List.pairwise_replicate], ?_⟩
  intro a ha b hb
  rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  omega

section Poly

open _root_.Formalism.L2.Col

variable {L : Type} [Field L]

theorem coeff_heckePolyOf (n q : ℕ) (a : ℕ → L) (k : ℕ) :
    (heckePolyOf n q a).coeff k = if k ≤ n then (-1) ^ k * (q : L) ^ (k * (k - 1) / 2) * a k else 0 := by
  unfold heckePolyOf
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Nat.lt_succ_iff]

end Poly

section Local

variable {D : D7} {V : HSp D}

def SphAt (J : Subgroup (GA D V)) (χ : GA D V → ℂ) (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ e f, IsPrimeIdem P e f → (∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) ∧ (∀ g ∈ J, SuppF V f g → χ g = 1) ∧
    ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, SuppF V f k₁ ∧ SuppF V (1 - f) k₂ ∧ k = k₁ * k₂

variable {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}

theorem primeIdem (he : IsIdemAt e P) : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩

theorem exists_loc (V : HSp D) (he : IsIdemAt e P) :
    ∃ L : Subgroup (GA D V), (∀ g, g ∈ L ↔ SuppF V (e + cA D e) g) ∧ L ≤ GfC V ∧
      ∀ g ∈ L, ∀ g', SuppF V (1 - (e + cA D e)) g' → Commute g g' := by
  obtain ⟨h1, -, h3, -⟩ := _root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  obtain ⟨a, b, c, -⟩ := h3 P e _ (primeIdem he)
  obtain ⟨⟨L, hL⟩, -, hc⟩ := h1 _ a b
  refine ⟨L, hL, fun g hg => c g ((hL g).1 hg), fun g hg g' hg' => hc _ g g' ?_ ((hL g).1 hg) hg'⟩
  rw [mul_sub, mul_one, a, sub_self]

theorem SphAt.loc_eq {J : Subgroup (GA D V)} {χ : GA D V → ℂ} (h : SphAt J χ P) (he : IsIdemAt e P) :
    {k | k ∈ (J : Set (GA D V)) ∧ SuppF V (e + cA D e) k} = locPart V (KsphC V ∅) e := by
  ext k
  exact and_congr_left fun hk => (h e _ (primeIdem he)).1 k hk

theorem SphAt.full {J : Subgroup (GA D V)} {χ : GA D V → ℂ} (h : SphAt J χ P) (he : IsIdemAt e P)
    {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hS : OffS D S P) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal)
    (h2 : ϖ ∉ P.asIdeal ^ 2) {d : List ℤ} (hd : d.Pairwise (fun a b => b ≤ a)) {α : GA D V} (hα : SuppAt e V α)
    (hdiv : DivAt V e (ϖ : D.host.E) d α) {R : Finset (GA D V)} (hR : ∀ γ ∈ R, SuppAt e V γ)
    (hc : IsCosetRep V (locPart V (KsphC V ∅) e) α R) : Hecke₂ V (J : Set (GA D V)) χ S P d R :=
  ⟨e, e + cA D e, ϖ, α, hS, primeIdem he, h1, h2, hd, (h e _ (primeIdem he)).1, (h e _ (primeIdem he)).2.1, hα, hdiv, hR,
    by rw [h.loc_eq he]; exact hc⟩

theorem SphAt.isDC {J : Subgroup (GA D V)} {χ : GA D V → ℂ} (h : SphAt J χ P) (he : IsIdemAt e P) {α : GA D V}
    (hα : SuppAt e V α) {R : Finset (GA D V)} (hR : ∀ γ ∈ R, SuppAt e V γ)
    (hc : IsCosetRep V (locPart V (KsphC V ∅) e) α R) : IsDC J α R := by
  obtain ⟨L, hL, -, hcom⟩ := exists_loc V he
  have hK : ∀ k, k ∈ locPart V (KsphC V ∅) e ↔ k ∈ J ⊓ L := fun k => by
    rw [← h.loc_eq he, Subgroup.mem_inf, hL]; rfl
  refine isDC_of_local (L := L) ((hL α).2 hα) (fun γ hγ => (hL γ).2 (hR γ hγ)) ?_ ?_ ?_
  · intro k hk
    obtain ⟨a, ha, b, hb, h1, h2, e⟩ := (h e _ (primeIdem he)).2.2 k hk
    exact ⟨a, ha, b, hb, (hL a).2 h1, hcom α ((hL α).2 hα) b h2, e⟩
  · intro γ hγ
    simpa only [hK] using (hc.1 γ hγ).2
  · simpa only [hK] using hc.2

theorem suppAt_inv (he : IsIdemAt e P) {α : GA D V} (h : SuppAt e V α) : SuppAt e V α⁻¹ := by
  obtain ⟨L, hL, -, -⟩ := exists_loc V he
  exact (hL _).1 (L.inv_mem ((hL α).2 h))

variable {S : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {M : DSModel V S}
  {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {c : Sys D}

theorem heckeOn_of_partFull {J J₀ : Subgroup (GA D V)} {χ χ₀ : GA D V → ℂ} (h : SphAt J χ P) (h₀ : SphAt J₀ χ₀ P)
    (hS : OffS D Sb P) {T : MMap M} (hT : T ∈ partFull θ M (J : Set (GA D V)) χ Sb c)
    (hinv : ∀ v, ∀ k ∈ J₀, ∀ g, T v (g * k) = T v g) {k : ℕ} (hk : k ≤ V.rank) {α : GA D V} (hα : IsHeckeAt V P k α)
    {R : Finset (GA D V)} (hR : IsDC J₀ α⁻¹ R) : heckeOn M R T = c P (splitLab V.rank k) • T := by
  obtain ⟨e, ϖ, he, h1, h2, hα⟩ := hα
  obtain ⟨-, hrep, -⟩ := _root_.GlobalTheory.SplitPlace.split_local V P e he
  have hi := suppAt_inv he hα.2.1
  obtain ⟨R', hR', hc⟩ := hrep α⁻¹ hi
  have hfull := h.full he hS h1 h2 (splitLab_pairwise _ k) hi (GlobalTheory.heckeElt_inv_divAt_splitLab V P e ϖ k α he h1 h2 hk hα) hR' hc
  have := ((mem_partFull θ M _ χ Sb c T).1 hT).2 P _ R' hfull
  ext v g
  have e1 := congrFun (this v) g
  rw [heckeLin_apply] at e1
  show heckeLin V R (T v) g = _
  rw [heckeLin_apply, sum_eq_of_isDC hR (h₀.isDC he hi hR' hc) (T v) (hinv v) g, e1]
  rfl

end Local

section Lev

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
  {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {M : DSModel V S}

theorem lev_of_mem_mult {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  induction hT using Submodule.span_induction with
  | mem T h => exact h.lev
  | zero => intro v k _ g; simp
  | add T T' _ _ h h' => intro v k hk g; simp [h v k hk g, h' v k hk g, mul_add]
  | smul a T _ h => intro v k hk g; simp [h v k hk g, mul_left_comm]

theorem mult_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) :
    Mult θ M J χ ≤ Mult θ M J' χ' :=
  Submodule.span_mono fun _ hT => ⟨hT.aut, hT.cusp, fun v k hk g => (h k hk).2 ▸ hT.lev v k (h k hk).1 g, hT.equiv, hT.cont⟩

variable {β : GL (Fin V.rank) (EAf D)} {r t : ℕ} {hr : r ≤ V.rank} {Pg : Finset (Pl D.host.E)}
  {χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}

theorem triv_le (Q : LevelP Pg r ℂ) (k : GA D V)
    (hk : k ∈ levG V β (datY _ r t 0 hr Pg ∅ (LevelP.triv Pg r ℂ) χ ξ Frm.B)) :
    k ∈ levG V β (datY _ r t 0 hr Pg ∅ Q χ ξ Frm.B) ∧ levChi V β (datY _ r t 0 hr Pg ∅ Q χ ξ Frm.B) k = 1 := by
  have h1 : rTup β (datY _ r t 0 hr Pg ∅ Q χ ξ Frm.B) (finE V k) = 1 := Subgroup.mem_bot.1 hk.2.2
  refine ⟨⟨hk.1, hk.2.1, ?_⟩, ?_⟩
  · rw [h1]; exact Subgroup.one_mem _
  · unfold levChi levFn
    rw [h1, blockDiagonalExtendByOnePrimeField_one]
    simp [datY]

theorem mult_le_triv (Q : LevelP Pg r ℂ) :
    Mult θ M (levS V β (datY _ r t 0 hr Pg ∅ Q χ ξ Frm.B)) (levChi V β (datY _ r t 0 hr Pg ∅ Q χ ξ Frm.B)) ≤
      Mult θ M (levS V β (datY _ r t 0 hr Pg ∅ (LevelP.triv Pg r ℂ) χ ξ Frm.B))
        (levChi V β (datY _ r t 0 hr Pg ∅ (LevelP.triv Pg r ℂ) χ ξ Frm.B)) :=
  mult_mono fun k hk => ⟨(triv_le Q k hk).1, (triv_le Q k hk).2.trans (triv_le _ k hk).2.symm⟩

variable {Pl0 : Type} {ok : Set Pl0} {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}

def GoodPl (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Pg : Finset (Pl D.host.E)) (ok : Set Pl0) (pl : Pl0 → Pl D.host.E)
    (q : Pl0 → ℕ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ P ∈ ok, (q P : ℂ) ≠ 0 ∧ OffS D Sb (pl P) ∧ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (pl P).asIdeal ≠ (pl P).asIdeal ∧
    ∀ L : LevDat D.host.E ℂ V.rank, L.Pg = Pg → L.Q = ∅ → SphAt (levG V β L) (levChi V β L) (pl P)

theorem heckeOn_lev (hg : GoodPl V β Pg ok pl q Sb) (Q : LevelP Pg r ℂ) {c : Sys D} {T : MMap M}
    (hT : T ∈ partFull θ M (levS V β (datY _ r t 0 hr Pg ∅ Q χ ξ Frm.B))
      (levChi V β (datY _ r t 0 hr Pg ∅ Q χ ξ Frm.B)) Sb c) {P : Pl0} (hP : P ∈ ok) {k : ℕ} (hk : k ≤ V.rank) {α : GA D V}
    (hα : IsHeckeAt V (pl P) k α) {R : Finset (GA D V)}
    (hR : IsDC (levG V β (datY _ r t 0 hr Pg ∅ (LevelP.triv Pg r ℂ) χ ξ Frm.B)) α⁻¹ R) :
    heckeOn M R T = c (pl P) (splitLab V.rank k) • T := by
  obtain ⟨-, h1, -, h2⟩ := hg P hP
  refine heckeOn_of_partFull (h2 _ rfl rfl) (h2 _ rfl rfl) h1 hT (fun v k hk g => ?_) hk hα hR
  rw [lev_of_mem_mult hT.1 v k (triv_le Q k hk).1 g, (triv_le Q k hk).2, one_mul]

theorem mem_hPart_iff {J : Subgroup (GA D V)} {Sg : Pl0 → ℂ[X]} {T : MMap M} :
    T ∈ hPart M J ok pl q Sg ↔ ∀ P ∈ ok, ∀ k, k ≤ V.rank → ∀ α, IsHeckeAt V (pl P) k α → ∀ R, IsDC J α⁻¹ R →
      heckeOn M R T = ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) • T := by
  unfold hPart
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_hPart_of_partFull (hg : GoodPl V β Pg ok pl q Sb) (Q : LevelP Pg r ℂ) {c : Sys D} {T : MMap M}
    (hT : T ∈ partFull θ M (levS V β (datY _ r t 0 hr Pg ∅ Q χ ξ Frm.B))
      (levChi V β (datY _ r t 0 hr Pg ∅ Q χ ξ Frm.B)) Sb c) {Sg : Pl0 → ℂ[X]}
    (hSg : ∀ P ∈ ok, Formalism.L2.Col.heckePolyOf V.rank (q P) (fun k => c (pl P) (splitLab V.rank k)) = Sg P) :
    T ∈ hPart M (levG V β (datY _ r t 0 hr Pg ∅ (LevelP.triv Pg r ℂ) χ ξ Frm.B)) ok pl q Sg := by
  rw [mem_hPart_iff]
  intro P hP k hk α hα R hR
  have hq := (hg P hP).1
  rw [heckeOn_lev hg Q hT hP hk hα hR, ← hSg P hP, coeff_heckePolyOf, if_pos hk, mul_div_cancel_left₀]
  simp [hq]

end Lev

section Record

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable {R : RealDat D A Ks} {F : Face D A} {s : ℕ}

theorem rank_zeroth_component_eq (D : D7) : (Yc D 0).rank = D.R.r := by
  rw [D.sp.Y_rank _ (min_le_right _ _)]; simp [Ranks.rankY]

theorem rank_weight_component_eq (i : Fin D.R.m) : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2

end Record

end GlobalTheory.HeckeParts

end
