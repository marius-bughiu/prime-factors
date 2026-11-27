(() => {
  "use strict";

  const normalize = text => text.toLowerCase().replace(/\s+/g, " ").trim();

  const alternateSpelling = text => text
    .replace(/\b\d{1,3}(?:,\d{3})+\b/g, number => number.replace(/,/g, ""))
    .replace(/[‐‑‒–−]/g, "-");

  function initialize() {
    const library = document.getElementById("finding-library");
    const tools = document.getElementById("finding-tools");
    const search = document.getElementById("finding-search");
    const clear = document.getElementById("finding-clear");
    const count = document.getElementById("finding-count");
    const empty = document.getElementById("finding-empty");
    if (!library || !tools || !search || !clear || !count || !empty) return;

    const buttons = Array.from(tools.querySelectorAll("[data-filter]"));
    const findings = Array.from(library.querySelectorAll("[data-finding]"), card => {
      const text = normalize(card.textContent);
      return { card, text, alternate: alternateSpelling(text) };
    });
    let category = "all";

    function searchMatches(finding, query, alternate) {
      return finding.text.includes(query) || finding.alternate.includes(alternate);
    }

    function render() {
      const query = normalize(search.value);
      const alternate = alternateSpelling(query);
      let total = 0;
      for (const finding of findings) {
        const matches = (category === "all" || category === finding.card.dataset.category) &&
          searchMatches(finding, query, alternate);
        finding.card.hidden = !matches;
        if (matches) total++;
      }
      for (const button of buttons) {
        button.setAttribute("aria-pressed", String(button.dataset.filter === category));
      }

      clear.hidden = !search.value && category === "all";
      empty.hidden = total > 0;
      count.textContent = total
        ? `Showing ${total} ${total === 1 ? "finding" : "findings"}`
        : "No matching findings";
    }

    search.addEventListener("input", render);
    for (const button of buttons) {
      button.addEventListener("click", () => {
        category = button.dataset.filter;
        render();
      });
    }
    clear.addEventListener("click", () => {
      search.value = "";
      category = "all";
      render();
      search.focus();
    });
    // Open a real target before the browser performs its normal fragment navigation.
    function reveal(hash) {
      if (!hash) return;
      let id;
      try {
        id = decodeURIComponent(hash.slice(1));
      } catch {
        return;
      }
      const target = document.getElementById(id);
      if (!target) return;
      const card = target.closest("[data-finding]");
      if (card && library.contains(card) && card.hidden) {
        const finding = findings.find(item => item.card === card);
        if (category !== "all" && category !== card.dataset.category) category = "all";
        const query = normalize(search.value);
        if (!searchMatches(finding, query, alternateSpelling(query))) search.value = "";
        render();
      }
      for (let details = target.closest("details"); details; details = details.parentElement?.closest("details")) {
        details.open = true;
      }
      return target;
    }

    document.addEventListener("click", event => {
      if (event.defaultPrevented || event.button !== 0 || event.metaKey || event.ctrlKey ||
          event.shiftKey || event.altKey) return;
      const link = event.target.closest?.("a[href]");
      if (!link || link.hasAttribute("download") || (link.target && link.target !== "_self")) return;
      const url = new URL(link.href, document.baseURI);
      if (url.origin === location.origin && url.pathname === location.pathname && url.search === location.search) {
        reveal(url.hash);
      }
    });

    function revealCurrent() {
      const target = reveal(location.hash);
      if (target) target.scrollIntoView();
    }
    tools.hidden = false;
    render();
    revealCurrent();
    window.addEventListener("hashchange", revealCurrent);
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", initialize, { once: true });
  else initialize();
})();
