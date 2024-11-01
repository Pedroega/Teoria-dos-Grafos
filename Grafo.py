from collections import deque
import heapq
import statistics
import psutil
import os
import time
import gzip
import random  # Para seleção aleatória de vértices

class Grafo:
    def __init__(self, num_vertices, representacao="lista"):
        self.num_vertices = num_vertices
        self.representacao = representacao
        self.num_arestas = 0

        if representacao == "lista":
            self.adjacencia = {i: [] for i in range(1, num_vertices + 1)}
        elif representacao == "matriz":
            self.adjacencia = [[float('inf')] * num_vertices for _ in range(num_vertices)]
        else:
            raise ValueError("Representação deve ser 'lista' ou 'matriz'.")

    @staticmethod
    def medir_memoria():
        process = psutil.Process(os.getpid())
        memoria = process.memory_info().rss / 1024 / 1024  # Converter para MB
        return memoria

    @staticmethod
    def comparar_memoria(arquivo):
        print("Carregando grafo usando lista de adjacência...")
        memoria_inicial = Grafo.medir_memoria()
        grafo_lista = Grafo.ler_grafo(arquivo, representacao="lista")
        memoria_lista = Grafo.medir_memoria() - memoria_inicial
        print(f"Memória usada pela lista de adjacência: {memoria_lista:.2f} MB")

    @staticmethod
    def ler_grafo(arquivo, representacao="lista"):
        with open(arquivo, 'r') as f:
            num_vertices = int(f.readline().strip())
            grafo = Grafo(num_vertices, representacao)
            for linha in f:
                v1, v2 = map(int, linha.strip().split())
                grafo.adicionar_aresta(v1, v2)
                grafo.num_arestas += 1
        return grafo

    @staticmethod
    def ler_grafo_ponderado(arquivo, representacao="lista"):
        open_file = gzip.open if arquivo.endswith(".gz") else open
        with open_file(arquivo, 'rt') as f:
            num_vertices = int(f.readline().strip())
            grafo = Grafo(num_vertices, representacao)
            for linha in f:
                v1, v2, peso = linha.strip().split()
                grafo.adicionar_aresta(int(v1), int(v2), float(peso))
        return grafo

    def adicionar_aresta(self, v1, v2, peso=1.0):
        if self.representacao == "lista":
            self.adjacencia[v1].append((v2, peso))
            self.adjacencia[v2].append((v1, peso))
        elif self.representacao == "matriz":
            self.adjacencia[v1 - 1][v2 - 1] = peso
            self.adjacencia[v2 - 1][v1 - 1] = peso
        self.num_arestas += 1

    def exibir_grafo(self):
        if self.representacao == "lista":
            for vertice, vizinhos in self.adjacencia.items():
                print(f'{vertice}: {vizinhos}')
        elif self.representacao == "matriz":
            for i in range(self.num_vertices):
                print(f'{i + 1}: {self.adjacencia[i]}')

    def grau_vertices(self):
        if self.representacao == "lista":
            graus = {v: len(self.adjacencia[v]) for v in self.adjacencia}
        elif self.representacao == "matriz":
            graus = {i + 1: sum(1 for peso in self.adjacencia[i] if peso != float('inf')) for i in range(self.num_vertices)}
        return graus

    def gerar_estatisticas(self):
        graus = list(self.grau_vertices().values())
        grau_minimo = min(graus)
        grau_maximo = max(graus)
        grau_medio = sum(graus) / len(graus)
        grau_mediana = statistics.median(graus)
        return {
            'num_vertices': self.num_vertices,
            'num_arestas': self.num_arestas,
            'grau_minimo': grau_minimo,
            'grau_maximo': grau_maximo,
            'grau_medio': grau_medio,
            'grau_mediana': grau_mediana
        }

    def buscar_vizinhos(self, vertice):
        if self.representacao == "lista":
            return self.adjacencia.get(vertice, [])
        elif self.representacao == "matriz":
            return [(i + 1, self.adjacencia[vertice - 1][i]) for i in range(self.num_vertices) if self.adjacencia[vertice - 1][i] != float('inf')]

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

    # Algoritmo de Dijkstra com vetor
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

    # Algoritmo de Dijkstra com heap
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

    # Função para calcular o tempo médio do Dijkstra
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

# ================== ESTUDOS DE CASO ==================

# Estudo de Caso 1: Cálculo de distância e caminho mínimo para o vértice 10
def estudo_de_caso_distancias(grafo):
    origem = 2722                                                              #altere para a origem que deseja
    destinos = [11365, 471365, 5709, 11386, 343930]                            #altere para os destinos que deseja
    
    print("=== Estudo de Caso 1: Distâncias e Caminhos Mínimos ===")
    for metodo in ["vetor", "heap"]:                          #altere para fazer o método vetor também
    #for metodo in ["heap"]:
        print(f"\nDistâncias e caminhos mínimos usando o método {metodo.upper()}:")
        for destino in destinos:
            distancia, caminho = grafo.calcular_distancia_e_caminho_minimo(origem, destino, metodo)
            print(f"Origem: {origem}, Destino: {destino} -> Distância: {distancia}, Caminho: {caminho}")

# Estudo de Caso 2: Tempo médio de execução do Dijkstra com e sem heap
def estudo_de_caso_tempo_medio(grafo, k=10):
    print("\n=== Estudo de Caso 2: Tempo Médio de Execução do Dijkstra ===")
    #for metodo in ["vetor", "heap"]:                         #altere para fazer o método vetor também
    for metodo in ["heap"]:
        tempo_medio = grafo.calcular_tempo_medio_dijkstra(k, metodo)
        print(f"Tempo médio para o método {metodo.upper()} com {k} execuções: {tempo_medio:.6f} segundos")

# Função principal para rodar os estudos de caso
def main():
    caminho_arquivo = os.path.join(os.path.dirname(__file__), "rede_colaboracao.txt")       #altere para o arquivo que deseja

    # Carregar o grafo do arquivo grafo_W_1.txt
    grafo = Grafo.ler_grafo_ponderado(caminho_arquivo, representacao="lista")

    # Executar Estudo de Caso 1
    estudo_de_caso_distancias(grafo)

    # Executar Estudo de Caso 2
    estudo_de_caso_tempo_medio(grafo, k=10)

# Executar a função main() ao rodar o arquivo
if __name__ == "__main__":
    main()
