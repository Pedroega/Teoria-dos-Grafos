from collections import deque
import heapq
import os
import time
import gzip
import statistics
import random  # Para seleção aleatória de vértices


class Grafo:
    def __init__(self, num_vertices, representacao="lista", direcionado=False):
        self.num_vertices = num_vertices
        self.representacao = representacao
        self.direcionado = direcionado
        self.num_arestas = 0

        if representacao == "lista":
            self.adjacencia = {i: [] for i in range(1, num_vertices + 1)}
        elif representacao == "matriz":
            self.adjacencia = [[float('inf')] * num_vertices for _ in range(num_vertices)]
        else:
            raise ValueError("Representação deve ser 'lista' ou 'matriz'.")

    @staticmethod
    def ler_grafo_ponderado(arquivo, representacao="lista", direcionado=False):
        open_file = gzip.open if arquivo.endswith(".gz") else open
        with open_file(arquivo, 'rt') as f:
            num_vertices = int(f.readline().strip())  # Primeira linha indica o número de vértices
            grafo = Grafo(num_vertices, representacao, direcionado)
            for linha in f:
                partes = linha.strip().split()
                if len(partes) == 3:  # Confirma que a linha tem exatamente 3 valores
                    v1, v2, peso = partes
                    grafo.adicionar_aresta(int(v1), int(v2), float(peso))
                else:
                    print(f"Erro: linha malformada '{linha.strip()}' ignorada.")
        return grafo


    def adicionar_aresta(self, v1, v2, peso=1.0):
        if self.representacao == "lista":
            self.adjacencia[v1].append((v2, peso))
            if not self.direcionado:
                self.adjacencia[v2].append((v1, peso))
        elif self.representacao == "matriz":
            self.adjacencia[v1 - 1][v2 - 1] = peso
            if not self.direcionado:
                self.adjacencia[v2 - 1][v1 - 1] = peso
        self.num_arestas += 1


    def buscar_vizinhos(self, vertice):
        if self.representacao == "lista":
            return self.adjacencia.get(vertice, [])
        elif self.representacao == "matriz":
            return [(i + 1, *self.adjacencia[vertice - 1][i]) for i in range(self.num_vertices) if self.adjacencia[vertice - 1][i] != float('inf')]

    def busca_largura(self, inicio):
        visitados = {v: False for v in range(1, self.num_vertices + 1)}
        nivel = {v: -1 for v in range(1, self.num_vertices + 1)}
        arvore = {v: None for v in range(1, self.num_vertices + 1)}
        fila = deque([inicio])

        visitados[inicio] = True
        nivel[inicio] = 0

        while fila:
            v = fila.popleft()
            for vizinho, _ in self.buscar_vizinhos(v):
                if not visitados[vizinho]:
                    visitados[vizinho] = True
                    nivel[vizinho] = nivel[v] + 1
                    arvore[vizinho] = v
                    fila.append(vizinho)

        return arvore, nivel

    def busca_profundidade(self, inicio):
        visitados = {v: False for v in range(1, self.num_vertices + 1)}
        nivel = {v: -1 for v in range(1, self.num_vertices + 1)}
        arvore = {v: None for v in range(1, self.num_vertices + 1)}

        def dfs(v, n):
            visitados[v] = True
            nivel[v] = n
            for vizinho, _ in self.buscar_vizinhos(v):
                if not visitados[vizinho]:
                    arvore[vizinho] = v
                    dfs(vizinho, n + 1)

        dfs(inicio, 0)
        return arvore, nivel

    def fluxo_maximo_ford_fulkerson(self, fonte, sumidouro):
        # Grafo residual inicial
        grafo_residual = Grafo(self.num_vertices, self.representacao, direcionado=True)
        for v in self.adjacencia:
            for u, peso in self.adjacencia[v]:
                # Usa o peso como capacidade
                grafo_residual.adicionar_aresta(v, u, peso)

        fluxo_maximo = 0
        while True:
            caminho, gargalo = self._encontrar_caminho_aumentante(grafo_residual, fonte, sumidouro)
            if not caminho:
                break
            fluxo_maximo += gargalo
            self._atualizar_fluxos(grafo_residual, caminho, gargalo)
        return fluxo_maximo


    def _encontrar_caminho_aumentante(self, grafo_residual, fonte, sumidouro):
        visitados = {v: False for v in range(1, grafo_residual.num_vertices + 1)}
        caminho = {}
        fila = deque([(fonte, float('inf'))])
        visitados[fonte] = True

        while fila:
            vertice_atual, fluxo_min = fila.popleft()
            for vizinho, capacidade in grafo_residual.buscar_vizinhos(vertice_atual):  # Apenas capacidade
                if not visitados[vizinho] and capacidade > 0:
                    caminho[vizinho] = (vertice_atual, capacidade)
                    fluxo_min = min(fluxo_min, capacidade)
                    if vizinho == sumidouro:
                        return caminho, fluxo_min
                    fila.append((vizinho, fluxo_min))
                    visitados[vizinho] = True
        return None, 0

    def _atualizar_fluxos(self, grafo_residual, caminho, gargalo):
        vertice_atual = max(caminho.keys())
        while vertice_atual in caminho:
            pai, capacidade = caminho[vertice_atual]
            # Reduzir capacidade na aresta direta
            for idx, (u, peso) in enumerate(grafo_residual.adjacencia[pai]):
                if u == vertice_atual:
                    grafo_residual.adjacencia[pai][idx] = (u, peso - gargalo)
            # Aumentar capacidade na aresta reversa
            for idx, (u, peso) in enumerate(grafo_residual.adjacencia[vertice_atual]):
                if u == pai:
                    grafo_residual.adjacencia[vertice_atual][idx] = (u, peso + gargalo)
            vertice_atual = pai


    # Implementação do algoritmo de Dijkstra com vetor e heap
    def calcular_distancia_e_caminho_minimo(self, inicio, destino, metodo="vetor"):
        if inicio not in self.adjacencia or destino not in self.adjacencia:
            print(f"Vértice {inicio} ou {destino} não existe no grafo.")
            return float('inf'), []

        if metodo == "vetor":
            distancias, caminho = self.dijkstra_vetor(inicio)
        elif metodo == "heap":
            distancias, caminho = self.dijkstra_heap(inicio)
        else:
            raise ValueError("Método deve ser 'vetor' ou 'heap'.")

        if distancias[destino] == float('inf'):
            print(f"Destino {destino} inatingível a partir de {inicio}.")
            return None, []

        caminho_minimo = []
        vertice_atual = destino
        while vertice_atual is not None:
            caminho_minimo.insert(0, vertice_atual)
            vertice_atual = caminho[vertice_atual]

        return round(distancias[destino], 2), caminho_minimo

    def dijkstra_vetor(self, inicio):
        distancias = {v: float('inf') for v in self.adjacencia.keys()}
        distancias[inicio] = 0
        visitados = {v: False for v in self.adjacencia.keys()}
        caminho = {v: None for v in self.adjacencia.keys()}

        for _ in range(len(self.adjacencia)):
            vertice_atual = min((distancias[v], v) for v in distancias if not visitados[v])[1]
            visitados[vertice_atual] = True

            for vizinho, peso in self.buscar_vizinhos(vertice_atual):
                if distancias[vizinho] > distancias[vertice_atual] + peso:
                    distancias[vizinho] = distancias[vertice_atual] + peso
                    caminho[vizinho] = vertice_atual

        return distancias, caminho

    def dijkstra_heap(self, inicio):
        distancias = {v: float('inf') for v in self.adjacencia.keys()}
        distancias[inicio] = 0
        caminho = {v: None for v in self.adjacencia.keys()}
        min_heap = [(0, inicio)]

        while min_heap:
            distancia_atual, vertice_atual = heapq.heappop(min_heap)

            if distancia_atual > distancias[vertice_atual]:
                continue

            for vizinho, peso in self.buscar_vizinhos(vertice_atual):
                if distancias[vizinho] > distancia_atual + peso:
                    distancias[vizinho] = distancia_atual + peso
                    caminho[vizinho] = vertice_atual
                    heapq.heappush(min_heap, (distancias[vizinho], vizinho))

        return distancias, caminho

    def calcular_tempo_medio_dijkstra(self, k=10, metodo="vetor"):
        tempos = []
        vertices = list(self.adjacencia.keys())

        for _ in range(k):
            inicio = random.choice(vertices)
            inicio_tempo = time.time()

            if metodo == "vetor":
                self.dijkstra_vetor(inicio)
            elif metodo == "heap":
                self.dijkstra_heap(inicio)
            else:
                raise ValueError("Método deve ser 'vetor' ou 'heap'.")

            tempos.append(time.time() - inicio_tempo)

        tempo_medio = sum(tempos) / k
        return round(tempo_medio, 6)


import os
import time

# Função para executar o estudo de caso
def estudo_de_caso_fluxo_maximo(grafo, fonte, sumidouro, num_execucoes=10):
    fluxos = []
    tempos = []

    for _ in range(num_execucoes):
        inicio = time.time()
        fluxo = grafo.fluxo_maximo_ford_fulkerson(fonte, sumidouro)
        tempos.append(time.time() - inicio)
        fluxos.append(fluxo)
    
    fluxo_medio = sum(fluxos) / len(fluxos)
    tempo_medio = sum(tempos) / len(tempos)

    print("=== Estudo de Caso: Fluxo Máximo ===")
    print(f"Fonte: {fonte}, Sumidouro: {sumidouro}")
    print(f"Fluxo máximo médio: {fluxo_medio:.2f}")
    print(f"Tempo médio de execução: {tempo_medio:.6f} segundos")

# Caminho do arquivo do grafo
caminho_arquivo = r"C:\trabalho_p1_grafos\src\grafo_rf_1.txt"

# Carregar o grafo direcionado e ponderado
grafo = Grafo.ler_grafo_ponderado(caminho_arquivo, direcionado=True, representacao="lista")

# Executar o estudo de caso com os vértices 1 (fonte) e 2 (sumidouro)
estudo_de_caso_fluxo_maximo(grafo, fonte=1, sumidouro=2, num_execucoes=10)
